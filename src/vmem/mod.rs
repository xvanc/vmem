/*
 * Copyright (c) 2022 xvanc <xvancm@gmail.com>
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors
 *    may be used to endorse or promote products derived from this software without
 *    specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */
/*	$NetBSD: subr_vmem.c,v 1.108 2022/05/31 08:43:16 andvar Exp $	*/
/*-
 * Copyright (c)2006,2007,2008,2009 YAMAMOTO Takashi,
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Based mainly on the paper by Jeff Bonwick and Jonathan Adams:
 *  `Magazines and Vmem: Extending the Slab Allocator to Many CPUs and Arbitrary Resources`
 * available here: https://www.usenix.org/legacy/event/usenix01/full_papers/bonwick/bonwick.pdf
 *
 * with reference to the implementation in NetBSD.
 */

//! Vmem Resource Allocator
//!
//! Vmem is a general-purpose resource allocator which provides constant-time performance
//! with low fragmentation.
//!
//! For a proper explanation of the allocator, see the paper
//! [Magazines and Vmem: Extending the Slab Allocator to Many CPUs and Arbitrary Resources](https://www.usenix.org/legacy/event/usenix01/full_papers/bonwick/bonwick.pdf).
//!
//! # Allocation Strategies
//!
//! Each allocation request can specify an allocation strategy.
//!
//! See the documentation for [`AllocStrategy`] for information on the individual allocation
//! strategies available.

#![warn(clippy::pedantic)]
#![allow(clippy::must_use_candidate)]

#[cfg(kernel)]
use crate::sync::mutex::{Mutex, MutexKind};
use alloc::borrow::Cow;
use core::{
    cmp, ptr,
    sync::atomic::{AtomicPtr, Ordering},
};
#[cfg(not(kernel))]
use spin::Mutex;

mod allocation_table;
mod segment_list;

use self::{
    allocation_table::AllocationTable,
    segment_list::{LinkedListLink, SegmentList, SegmentQueue},
};

const LOGGING: bool = cfg!(any(vmem_log, feature = "log"));

const NUM_FREE_LISTS: usize = usize::BITS as usize;
const NUM_HASH_BUCKETS: usize = 16;
const NUM_STATIC_BTS: usize = 4096;

fn freelist_for_size(size: usize) -> usize {
    NUM_FREE_LISTS - size.leading_zeros() as usize - 1
}

/// Bootstrap the vmem system
///
/// # Safety
///
/// This function must only be called once.
#[allow(clippy::needless_range_loop)]
pub unsafe fn bootstrap() {
    // Init the list of static boundary tags.
    for i in 0..NUM_STATIC_BTS {
        let bt = ptr::addr_of_mut!(STATIC_BOUNDARY_TAG_STORAGE[i]);
        (*bt).segment_queue_link.next = STATIC_BOUNDARY_TAGS.load(Ordering::Relaxed);
        STATIC_BOUNDARY_TAGS.store(bt, Ordering::Relaxed);
    }
}

/// Align to the next multiple of `align` which is greater-than or equal-to `x`
///
/// `align` must be a power-of-two.
const fn pow2_align_up(x: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two(), "`align` must be a power-of-two");
    (x.wrapping_neg() & align.wrapping_neg()).wrapping_neg()
}

/// Checks if the range `start ..= end` crosses a multiple of `align`
///
/// `align` must be a power-of-two.
const fn pow2_crosses_boundary(start: usize, end: usize, align: usize) -> bool {
    debug_assert!(
        align == 0 || align.is_power_of_two(),
        "`align` must be a power-of-two"
    );
    (start ^ end) & align.wrapping_neg() != 0
}

#[derive(Debug)]
pub enum Error {
    OutOfMemory,
    OutOfTags,
}

#[cfg(notyet)]
#[cfg(kernel)]
impl From<Error> for crate::sys::Errno {
    fn from(err: Error) -> crate::sys::Errno {
        crate::sys::Errno::OutOfMemory
    }
}

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum BtKind {
    #[default]
    Span,
    SpanImported,
    Free,
    Used,
}

/// Boundary Tag
///
/// A boundary tag is allocated for each span and each free or used segment within each span.
#[derive(Debug, Default)]
struct Bt {
    kind: BtKind,
    base: usize,
    size: usize,

    /// Segment List Link
    ///
    /// Each boundary tag is linked into a list of all span/segments owned by an arena.
    segment_list_link: LinkedListLink,

    /// Segment Queue Link
    ///
    /// Based on the segment's type, the boundary tag is also linked into one of two "queues":
    ///
    /// - [`Free`](BtKind::Free) tags are linked into a power-of-two freelist based on their size.
    ///
    /// - [`Used`][BtKind::Used] tags are linked into an allocation hash table for easy lookup
    ///   when freed.
    segment_queue_link: LinkedListLink,
}

/// Boundary Tag Allocation
impl Bt {
    /// Allocate a new boundary tag
    fn alloc(base: usize, size: usize, kind: BtKind) -> Result<*mut Bt> {
        let bt = alloc_static_bt()?;
        unsafe {
            *bt = Bt::new(base, size, kind);
        }
        Ok(bt)
    }

    /// Free a boundary tag
    unsafe fn free(bt: *mut Bt) {
        free_static_bt(bt);
    }
}

impl Bt {
    /// Create a new boundary tag
    const fn new(base: usize, size: usize, kind: BtKind) -> Bt {
        Self {
            kind,
            base,
            size,
            segment_list_link: LinkedListLink::new(),
            segment_queue_link: LinkedListLink::new(),
        }
    }

    /// Returns `true` if this boundary tag is a span marker.
    const fn is_span(&self) -> bool {
        matches!(self.kind, BtKind::Span | BtKind::SpanImported)
    }

    /// Check if a segment can satisfy an allocation
    ///
    /// If successful, returns the offset into the segment at which an allocation respecting
    /// the given constraints could be made.
    ///
    /// # Panics
    ///
    /// The caller must have already checked that the span is large enough to potentially
    /// satisfy the allocation.
    fn can_satisfy(&self, layout: &Layout) -> Option<usize> {
        // Align up while respecting `phase`.
        const fn pow2_align_up_phase(start: usize, align: usize, phase: usize) -> usize {
            pow2_align_up(start - phase, align) + phase
        }

        debug_assert!(matches!(self.kind, BtKind::Free));
        debug_assert!(
            self.size >= layout.size,
            "sanity: `can_satisfy` called on insufficiently-sized tag"
        );

        // I don't fully understand why this works, thank you NetBSD <3

        let mut start = self.base;
        let mut end = self.base + self.size - 1;

        start = cmp::max(start, layout.minaddr);
        end = cmp::min(end, layout.maxaddr);
        if start > end {
            return None;
        }

        start = pow2_align_up_phase(start, layout.align, layout.phase);
        if start < self.base {
            start += layout.align;
        }

        if pow2_crosses_boundary(start, start + layout.size - 1, layout.nocross) {
            start = pow2_align_up_phase(start, layout.nocross, layout.phase);
        }

        if start <= end && end - start >= layout.size - 1 {
            Some(start - self.base)
        } else {
            None
        }
    }
}

static mut STATIC_BOUNDARY_TAG_STORAGE: [Bt; NUM_STATIC_BTS] = {
    const UNINIT: Bt = Bt::new(0, 0, BtKind::Span);
    [UNINIT; NUM_STATIC_BTS]
};

static STATIC_BOUNDARY_TAGS: AtomicPtr<Bt> = AtomicPtr::new(ptr::null_mut());

fn alloc_static_bt() -> Result<*mut Bt> {
    let mut bt;
    loop {
        bt = STATIC_BOUNDARY_TAGS.load(Ordering::Relaxed);
        if bt.is_null() {
            break Err(Error::OutOfTags);
        }
        let new_head = unsafe { (*bt).segment_queue_link.next };
        if STATIC_BOUNDARY_TAGS
            .compare_exchange_weak(bt, new_head, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            break Ok(bt);
        }
        core::hint::spin_loop();
    }
}

unsafe fn free_static_bt(bt: *mut Bt) {
    debug_assert!(!bt.is_null(), "sanity: freeing null tag");

    loop {
        let old_head = STATIC_BOUNDARY_TAGS.load(Ordering::Relaxed);
        (*bt).segment_queue_link.next = old_head;
        if STATIC_BOUNDARY_TAGS
            .compare_exchange_weak(old_head, bt, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            break;
        }
        core::hint::spin_loop();
    }
}

#[derive(Debug)]
struct FreeLists {
    lists: [SegmentQueue; NUM_FREE_LISTS],
}

impl FreeLists {
    unsafe fn insert(&mut self, bt: *mut Bt) {
        self.lists[freelist_for_size((*bt).size)].insert_head(bt);
    }

    unsafe fn remove(&mut self, bt: *mut Bt) {
        self.lists[freelist_for_size((*bt).size)].remove(bt);
    }
}

/// Layout of a constrained allocation
#[derive(Clone, Copy, Debug)]
pub struct Layout {
    size: usize,
    align: usize,
    phase: usize,
    nocross: usize,
    minaddr: usize,
    maxaddr: usize,
}

impl Layout {
    /// Create a new layout describing a region of `size` bytes.
    ///
    /// # Panics
    ///
    /// This function will panic if `size` is `0`.
    pub const fn new(size: usize) -> Layout {
        assert!(size > 0, "`size` must be greater than zero");
        Self {
            size,
            align: 0,
            phase: 0,
            nocross: 0,
            minaddr: 0,
            maxaddr: usize::MAX,
        }
    }

    /// Request an allocation aligned to a specific boundary
    ///
    /// # Panics
    ///
    /// `align` must be a nonzero power-of-two.
    #[must_use]
    pub const fn align(mut self, align: usize) -> Layout {
        assert!(align.is_power_of_two(), "`align` must be a power-of-two");
        assert!(
            self.nocross == 0 || align >= self.nocross,
            "`align` must be greater-than or equal-to `nocross`"
        );
        self.align = align;
        self
    }

    /// Specify a specific offset from the layout's alignment
    #[must_use]
    pub const fn phase(mut self, phase: usize) -> Layout {
        self.phase = phase;
        self
    }

    /// Specify a specific boundary which the allocation must not cross.
    ///
    /// The region described by this layout will not cross a `nocross`-aligned boundary.
    ///
    /// # Panics
    ///
    /// `nocross` must be a power-of-two
    #[must_use]
    pub const fn nocross(mut self, nocross: usize) -> Layout {
        assert!(
            nocross >= self.size,
            "`nocross` must be greater-than or equal-to `size`"
        );
        self.nocross = nocross;
        self
    }

    /// Specify a range which the allocation must be made within
    ///
    /// # Panics
    ///
    /// The end of `range` must be greater than the beginning.
    #[must_use]
    pub const fn within(mut self, range: core::ops::RangeInclusive<usize>) -> Layout {
        assert!(
            *range.start() <= *range.end(),
            "`minaddr` must be less-than or equal-to `maxaddr`"
        );
        self.minaddr = *range.start();
        self.maxaddr = *range.end();
        self
    }

    #[inline]
    pub const fn get_size(&self) -> usize {
        self.size
    }

    #[inline]
    pub const fn get_align(&self) -> usize {
        self.align
    }

    #[inline]
    pub const fn get_phase(&self) -> usize {
        self.phase
    }

    #[inline]
    pub const fn get_nocross(&self) -> usize {
        self.nocross
    }

    #[inline]
    pub const fn get_minaddr(&self) -> usize {
        self.minaddr
    }

    #[inline]
    pub const fn get_maxaddr(&self) -> usize {
        self.maxaddr
    }

    /// Round the size and alignment of this layout to `quantum`.
    fn quantum_align(&mut self, quantum: usize) {
        debug_assert!(
            quantum.is_power_of_two(),
            "sanity: quantum is not a power-of-two"
        );
        self.size = cmp::max(quantum, self.size);
        self.align = cmp::max(quantum, self.align);
    }
}

/// Allocation Strategy
#[repr(u32)]
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, Default, Debug, Eq, PartialEq)]
pub enum AllocStrategy {
    /// Best Fit
    ///
    /// This strategy searches the freelist for the smallest segment which can satisfy the request.
    BestFit = 0,
    /// Instant Fit
    ///
    /// This strategy searches the freelist for the next power-of-two which is greater-than or
    /// equal-to the size of the request. Any segment on this list is guaranteed to be large
    ///  enough to satisfy the request.
    #[default]
    InstantFit,
    /// Next Fit
    ///
    /// This strategy ignores the freelist and instead searches the arena for the next segment
    /// after the one previously allocated. This strategy is particularly useful for resources
    /// such as process IDs, to cycle through all available IDs before recycling old ones.
    NextFit,
}

/// Types from which a [`Vmem`] arena can import spans.
///
/// # Safety
pub unsafe trait Source: Send + Sync {
    /// Import a span from this source.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if no resources are currently available.
    fn import(&self, size: usize) -> Result<usize>;

    /// Release a segment back to its source
    ///
    /// # Safety
    ///
    /// The segment `base .. base + size` must have been previously allocated by a call to
    /// [`import()`](Source::import) on the same source.
    unsafe fn release(&self, base: usize, size: usize);
}

unsafe impl Source for Vmem<'_, '_> {
    fn import(&self, size: usize) -> Result<usize> {
        self.alloc(size, AllocStrategy::BestFit)
    }

    unsafe fn release(&self, base: usize, size: usize) {
        self.free(base, size);
    }
}

/// Vmem Arena
///
/// See [the module-level documentation](self) for more information.
pub struct Vmem<'name, 'src> {
    name: Cow<'name, str>,
    quantum: usize,
    source: Option<&'src dyn Source>,
    l: Mutex<VmemInner>,
}

unsafe impl Send for Vmem<'_, '_> {}
unsafe impl Sync for Vmem<'_, '_> {}

/// The inner, locked portion of a [`Vmem`] arena
struct VmemInner {
    segment_list: SegmentList,
    allocation_table: AllocationTable,
    freelist: FreeLists,
    last_alloc: *mut Bt,
    bytes_total: usize,
    bytes_allocated: usize,
}

impl<'name, 'src> Vmem<'name, 'src> {
    /// Create a new arena
    ///
    /// # Panics
    ///
    /// `quantum` must be a power-of-two.
    #[allow(clippy::must_use_candidate)]
    pub const fn new(
        name: Cow<'name, str>,
        quantum: usize,
        source: Option<&'src dyn Source>,
        #[cfg(kernel)] mtx_kind: MutexKind,
    ) -> Self {
        Self::new_inner(
            name,
            quantum,
            source,
            #[cfg(kernel)]
            mtx_kind,
        )
    }

    /// Create a new arena with an initial span
    ///
    /// # Errors
    ///
    /// This function errors only if resources cannot be allocated to describe the new span.
    ///
    /// # Panics
    ///
    /// `quantum` must be a power-of-two.
    pub fn with_span(
        name: Cow<'name, str>,
        quantum: usize,
        source: Option<&'src dyn Source>,
        #[cfg(kernel)] mtx_kind: MutexKind,
        base: usize,
        size: usize,
    ) -> Result<Self> {
        let vmem = Self::new_inner(
            name,
            quantum,
            source,
            #[cfg(kernel)]
            mtx_kind,
        );
        vmem.add(base, size)?;
        Ok(vmem)
    }
}

impl<'name, 'src> Vmem<'name, 'src> {
    #[allow(clippy::must_use_candidate)]
    const fn new_inner(
        name: Cow<'name, str>,
        quantum: usize,
        source: Option<&'src dyn Source>,
        #[cfg(kernel)] mtx_kind: MutexKind,
    ) -> Self {
        assert!(
            quantum.is_power_of_two(),
            "`quantum` must be a power-of-two"
        );
        let inner = VmemInner {
            allocation_table: AllocationTable::new(),
            freelist: FreeLists {
                lists: [SegmentQueue::EMPTY; NUM_FREE_LISTS],
            },
            segment_list: SegmentList::new(),
            last_alloc: ptr::null_mut(),
            bytes_total: 0,
            bytes_allocated: 0,
        };
        Self {
            name,
            quantum,
            source,
            l: Mutex::new(
                #[cfg(kernel)]
                mtx_kind,
                inner,
            ),
        }
    }
}

impl Vmem<'_, '_> {
    #[track_caller]
    fn alloc_constrained_inner(
        &self,
        mut layout: Layout,
        mut strategy: AllocStrategy,
    ) -> Result<usize> {
        layout.quantum_align(self.quantum);

        let mut l = self.l.lock();

        // Select a segment from which to allocate.
        #[allow(clippy::never_loop)]
        let (bt, alloc_offset) = loop {
            let opt = match strategy {
                AllocStrategy::BestFit => l.choose_best_fit(&layout),
                AllocStrategy::InstantFit => l.choose_instant_fit(&layout),
                AllocStrategy::NextFit => l.choose_next_fit(&layout),
            };

            if let Some(bt) = opt {
                break bt;
            }

            // If Instant Fit didn't work, fall back to Best Fit.
            if strategy == AllocStrategy::InstantFit {
                strategy = AllocStrategy::BestFit;
                continue;
            }

            // If we have a source, import from it.
            if let Some(source) = self.source {
                let size = (0x1000 * 64).max(layout.size); // ?????
                if let Ok(base) = source.import(size) {
                    l.add(
                        base,
                        size,
                        BtKind::SpanImported,
                        #[cfg(not(kernel))]
                        self.name(),
                    )?;
                    continue;
                }
            }

            // TODO: This is where we'd wait for more memory.

            return Err(Error::OutOfMemory);
        };

        // Ensure spooky events have not occurred.
        debug_assert!(!bt.is_null(), "sanity: allocated null tag");

        unsafe {
            // Remove the segment from the free list.
            l.freelist.remove(bt);

            // Split the segment up if needed.
            if let Err(err) = l.split(bt, alloc_offset, layout.size) {
                l.freelist.insert(bt);
                return Err(err);
            }
            (*bt).kind = BtKind::Used;

            // Insert the segment into the allocation table.
            l.allocation_table.insert(bt);
            l.last_alloc = bt;

            l.bytes_allocated += layout.size;

            Ok((*bt).base)
        }
    }

    /// Returns the name of this arena.
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the total number of bytes managed by the arena
    #[inline]
    pub fn capacity(&self) -> usize {
        self.l.lock().bytes_total
    }

    /// Returns the total number of bytes currently allocated from the arena
    #[inline]
    pub fn capacity_used(&self) -> usize {
        self.l.lock().bytes_allocated
    }

    /// Returns the total number of bytes in the arena available for allocation
    #[inline]
    pub fn capacity_free(&self) -> usize {
        let l = self.l.lock();
        l.bytes_total - l.bytes_allocated
    }

    /// Add a span to this arena
    ///
    /// # Errors
    ///
    /// This function errors only if resources cannot be allocated to describe the new span.
    pub fn add(&self, base: usize, size: usize) -> Result<()> {
        self.l.lock().add(
            base,
            size,
            BtKind::Span,
            #[cfg(not(kernel))]
            self.name(),
        )?;
        Ok(())
    }

    /// Allocate `size` bytes from this arena.
    ///
    /// # Errors
    ///
    /// This function errors if the requested allocation cannot be satisfied by this arena.
    pub fn alloc(&self, size: usize, strategy: AllocStrategy) -> Result<usize> {
        self.alloc_constrained(Layout::new(size).align(self.quantum), strategy)
    }

    /// Free a segment allocated by [`alloc()`](Vmem::alloc)
    ///
    /// # Safety
    ///
    /// The segment must have previously been allocated by a call to [`alloc()`](Vmem::alloc).
    ///
    /// # Panics
    ///
    /// This function panics if the segment cannot be found in the allocation hash table.
    pub unsafe fn free(&self, base: usize, size: usize) {
        self.free_constrained(base, size);
    }

    /// Allocate a segment which respects the constraints of `layout`.
    ///
    /// # Errors
    ///
    /// This function errors if the requested allocation cannot be satisfied by this arena.
    #[track_caller]
    pub fn alloc_constrained(&self, layout: Layout, strategy: AllocStrategy) -> Result<usize> {
        #[cfg(not(kernel))]
        {
            let x = self.alloc_constrained_inner(layout, strategy);
            if LOGGING {
                log::trace!(
                    "{}: alloc_constrained({:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:?}) => {:?}",
                    self.name,
                    layout.size,
                    layout.align,
                    layout.phase,
                    layout.nocross,
                    layout.minaddr,
                    layout.maxaddr,
                    strategy,
                    HexResult(&x)
                );
            }
            x
        }
        #[cfg(kernel)]
        self.alloc_constrained_inner(layout, strategy)
    }

    /// Free a segment allocated by [`alloc_constrained()`](Vmem::alloc_constrained)
    ///
    /// # Safety
    ///
    /// The segment must have previously been allocated by a call to [`alloc_constrained()`](Vmem::alloc_constrained).
    ///
    /// # Panics
    ///
    /// This function panics if a matching segment cannot be found in the allocation table.
    pub unsafe fn free_constrained(&self, base: usize, size: usize) {
        #[cfg(not(kernel))]
        if LOGGING {
            log::trace!("{}: free_constrained({:#x}, {:#x})", self.name, base, size);
        }

        let mut l = self.l.lock();

        // Find the tag for the allocation.
        // If it doesn't exist this is very likely a double-free.
        let bt = l
            .allocation_table
            .find(base)
            .expect("freed tag not in allocation table");

        let (mut free_bts, mut release_span) = ([ptr::null_mut(); 2], ptr::null_mut());

        'b: {
            unsafe {
                let alloc_size = cmp::max(self.quantum, size);

                // The sizes should match up, otherwise this is very likely
                // a double-free. Since a tag was found for the address this
                // also likely means memory corruption has occurred.
                assert!(
                    (*bt).size == alloc_size,
                    "freed size does not match allocation"
                );

                l.allocation_table.remove(bt);

                let (prev, next) = l.merge(bt);

                // Check if the entire span is now free.
                if (*prev).is_span() && (next.is_null() || (*next).is_span()) {
                    // If the span was imported release it back to its source.
                    if (*prev).kind == BtKind::SpanImported {
                        // Remove the span marker and the now free segment from the
                        // arena's segment list.

                        if l.last_alloc == bt {
                            if (*bt).segment_list_link.next.is_null() {
                                l.last_alloc = l.segment_list.head;
                            } else {
                                l.last_alloc = (*bt).segment_list_link.next;
                            }
                        }

                        l.segment_list.remove(prev);
                        l.segment_list.remove(bt);

                        release_span = prev;
                        free_bts[0] = prev;
                        free_bts[1] = bt;
                        break 'b;
                    }
                }

                (*bt).kind = BtKind::Free;
                l.freelist.insert(bt);
                l.bytes_allocated -= alloc_size;
            }
        }

        if l.last_alloc == bt {
            if (*bt).segment_list_link.next.is_null() {
                l.last_alloc = l.segment_list.head;
            } else {
                l.last_alloc = (*bt).segment_list_link.next;
            }
        }

        // Release the lock before freeing everything.
        drop(l);

        if !release_span.is_null() {
            // We must have a source if we have an imported span.
            self.source
                .expect("have imported span with no source")
                .release((*release_span).base, (*release_span).size);
        }
        if !free_bts[0].is_null() {
            Bt::free(free_bts[0]);
            Bt::free(free_bts[1]);
        }
    }

    #[doc(hidden)]
    pub fn log_segment_list(&self) {
        self.l.lock().print_segment_list(self.name());
    }
}

impl VmemInner {
    fn choose_instant_fit(&mut self, layout: &Layout) -> Option<(*mut Bt, usize)> {
        // By rounding `layout.size` to the next power-of-two >= itself, we start with
        // the first free list which is guaranteed to have segments large enough to
        // satisfy the allocation.
        let first = freelist_for_size(layout.size.next_power_of_two());
        for list in self.freelist.lists[first..].iter_mut() {
            if !list.head.is_null() {
                if let Some(offset) = unsafe { (*list.head).can_satisfy(layout) } {
                    return Some((list.head, offset));
                }
            }
        }
        None
    }

    fn choose_best_fit(&mut self, layout: &Layout) -> Option<(*mut Bt, usize)> {
        let first = freelist_for_size(layout.size);
        for list in self.freelist.lists[first..].iter_mut() {
            let mut bt = list.head;
            while !bt.is_null() {
                unsafe {
                    if let Some(offset) = (*bt).can_satisfy(layout) {
                        return Some((bt, offset));
                    }
                    bt = (*bt).segment_queue_link.next;
                }
            }
        }
        None
    }

    fn choose_next_fit(&mut self, layout: &Layout) -> Option<(*mut Bt, usize)> {
        // Start searching from the most recent allocation.
        let start = if self.last_alloc.is_null() {
            self.segment_list.head
        } else {
            self.last_alloc
        };
        let mut bt = start;

        if bt.is_null() {
            // Arena is empty.
            return None;
        }

        loop {
            unsafe {
                if (*bt).kind == BtKind::Free {
                    if let Some(offset) = (*bt).can_satisfy(layout) {
                        break Some((bt, offset));
                    }
                }

                if (*bt).segment_list_link.next.is_null() {
                    // Reached the end, wrap back around.
                    bt = self.segment_list.head;
                } else {
                    bt = (*bt).segment_list_link.next;
                }
                if bt == start {
                    // We've searched the entire arena.
                    break None;
                }
            }
        }
    }

    fn print_segment_list(&self, name: &str) {
        let mut bt = self.segment_list.head;

        log::info!("{name}");
        while !bt.is_null() {
            unsafe {
                log::info!(
                    "{:?}: base: {:#x}, size: {:#x}",
                    (*bt).kind,
                    (*bt).base,
                    (*bt).size
                );
                bt = (*bt).segment_list_link.next;
            }
        }
    }

    fn add(
        &mut self,
        base: usize,
        size: usize,
        span_kind: BtKind,
        #[cfg(not(kernel))] name: &str,
    ) -> Result<()> {
        #[cfg(not(kernel))]
        if LOGGING {
            log::trace!("{}: add({base:#x}, {size:#x}, {span_kind:?})", name);
        }

        let span = Bt::alloc(base, size, span_kind)?;
        let free = Bt::alloc(base, size, BtKind::Free)?;
        unsafe {
            self.segment_list.insert_ordered_span(span, free);
            self.freelist.insert(free);
        }
        self.bytes_total += size;

        Ok(())
    }

    unsafe fn split(&mut self, bt: *mut Bt, offset: usize, size: usize) -> Result<()> {
        assert!(!bt.is_null());
        // `can_satisfy` shouldn't return an insufficiently-sized tag
        assert!((*bt).size >= offset + size);

        let bt_base = (*bt).base;
        let bt_size = (*bt).size;
        let rem_front = offset;
        let rem_back = bt_size - offset - size;

        (*bt).base += offset;
        (*bt).size = size;

        if rem_front > 0 {
            let free = Bt::alloc(bt_base, rem_front, BtKind::Free)?;
            self.segment_list.insert_ordered(free);
            self.freelist.insert(free);
        }

        if rem_back > 0 {
            let free = Bt::alloc(bt_base + offset + size, rem_back, BtKind::Free)?;
            self.segment_list.insert_ordered(free);
            self.freelist.insert(free);
        }

        Ok(())
    }

    /// Attempt to merge neighbors into `bt`.
    ///
    /// Returns the new `prev` and `next` pointers, which will have already been updated in `bt`.
    unsafe fn merge(&mut self, bt: *mut Bt) -> (*mut Bt, *mut Bt) {
        debug_assert!(!bt.is_null());
        debug_assert!(!matches!((*bt).kind, BtKind::Span | BtKind::SpanImported));

        let mut prev = (*bt).segment_list_link.prev;
        let mut next = (*bt).segment_list_link.next;

        // Any non-span tag should always be preceded by at least a span tag.
        debug_assert!(!prev.is_null());

        if (*prev).kind == BtKind::Free && (*prev).base + (*prev).size == (*bt).base {
            (*bt).base = (*prev).base;
            (*bt).size += (*prev).size;
            let old = prev;
            prev = (*prev).segment_list_link.prev;
            self.freelist.remove(old);
            self.segment_list.remove(old);
            Bt::free(old);
        }

        // We want to prevent merging the next block into this one if `last_alloc` still
        // points this tag. Otherwise we'd start recycling allocations too quickly.
        if !next.is_null()
            && self.last_alloc != bt
            && (*next).kind == BtKind::Free
            && (*bt).base + (*bt).size == (*next).base
        {
            (*bt).size += (*next).size;
            let old = next;
            next = (*next).segment_list_link.next;
            self.freelist.remove(old);
            self.segment_list.remove(old);
            Bt::free(old);
        }

        (prev, next)
    }
}

impl Drop for Vmem<'_, '_> {
    fn drop(&mut self) {
        let l = self.l.lock();
        assert!(
            l.allocation_table.is_empty(),
            "dropping arena with live allocations"
        );
        let mut bt = l.segment_list.head;
        while !bt.is_null() {
            let ptr = bt;
            unsafe {
                bt = (*bt).segment_list_link.next;
                Bt::free(ptr);
            }
        }
    }
}
struct HexResult<'a>(&'a Result<usize>);

impl core::fmt::Debug for HexResult<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.0 {
            Ok(base) => write!(f, "Ok({base:#x})"),
            Err(ref err) => write!(f, "Err({err:?})"),
        }
    }
}
