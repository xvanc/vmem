use super::Bt;
use core::ptr;

#[derive(Debug)]
pub struct LinkedListLink {
    pub(super) prev: *mut Bt,
    pub(super) next: *mut Bt,
}

impl Default for LinkedListLink {
    fn default() -> Self {
        Self::new()
    }
}

impl LinkedListLink {
    pub(super) const fn new() -> LinkedListLink {
        Self {
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }
    }
}

/// Segment list
///
/// Manages a collection of [`Bt`]s using `segment_list_link`.
#[derive(Debug)]
pub struct SegmentList {
    pub(super) head: *mut Bt,
    pub(super) tail: *mut Bt,
}

impl Default for SegmentList {
    fn default() -> Self {
        Self::new()
    }
}

impl SegmentList {
    pub(super) const fn new() -> Self {
        Self {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        }
    }

    fn insertion_point(&self, base: usize) -> (*mut Bt, *mut Bt) {
        let mut prev = ptr::null_mut();
        let mut next = self.head;
        while !next.is_null() {
            unsafe {
                if (*next).base > base {
                    break;
                }
                prev = next;
                next = (*next).segment_list_link.next;
            }
        }
        (prev, next)
    }

    pub(super) unsafe fn insert_ordered(&mut self, bt: *mut Bt) {
        let (prev, next) = self.insertion_point((*bt).base);

        (*bt).segment_list_link.prev = prev;
        (*bt).segment_list_link.next = next;

        if prev.is_null() {
            self.head = bt;
        } else {
            (*prev).segment_list_link.next = bt;
        }
        if next.is_null() {
            self.tail = bt;
        } else {
            (*next).segment_list_link.prev = bt;
        }
    }

    pub(super) unsafe fn insert_ordered_span(&mut self, span: *mut Bt, free: *mut Bt) {
        debug_assert!((*span).base == (*free).base);
        debug_assert!((*span).size == (*free).size);

        let (prev, next) = self.insertion_point((*span).base);

        (*span).segment_list_link.prev = prev;
        (*span).segment_list_link.next = free;
        (*free).segment_list_link.prev = span;
        (*free).segment_list_link.next = next;

        if prev.is_null() {
            self.head = span;
        } else {
            (*prev).segment_list_link.next = span;
        }
        if next.is_null() {
            self.tail = free;
        } else {
            (*next).segment_list_link.prev = free;
        }
    }

    pub(super) unsafe fn remove(&mut self, bt: *mut Bt) {
        let prev = (*bt).segment_list_link.prev;
        let next = (*bt).segment_list_link.next;

        if prev.is_null() {
            self.head = next;
        } else {
            (*prev).segment_list_link.next = next;
        }
        if next.is_null() {
            self.tail = prev;
        } else {
            (*next).segment_list_link.prev = prev;
        }
    }
}

/// Segment queue
///
/// Manages a collection of [`Bt`]s using `segment_queue_link`.
#[derive(Debug)]
pub struct SegmentQueue {
    pub(super) head: *mut Bt,
    pub(super) tail: *mut Bt,
}

impl SegmentQueue {
    pub const EMPTY: Self = Self::new();

    pub(super) const fn new() -> Self {
        Self {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        }
    }

    pub(super) unsafe fn insert_head(&mut self, bt: *mut Bt) {
        let prev = ptr::null_mut();
        let next = self.head;
        (*bt).segment_queue_link.prev = prev;
        (*bt).segment_queue_link.next = next;
        self.head = bt;
        if next.is_null() {
            self.tail = bt;
        } else {
            (*next).segment_queue_link.prev = bt;
        }
    }

    pub(super) fn pop_head(&mut self) -> Option<*mut Bt> {
        let bt = self.head;
        if bt.is_null() {
            None
        } else {
            unsafe { self.remove(bt) };
            Some(bt)
        }
    }

    pub(super) unsafe fn remove(&mut self, bt: *mut Bt) {
        let prev = (*bt).segment_queue_link.prev;
        let next = (*bt).segment_queue_link.next;
        if prev.is_null() {
            self.head = next;
        } else {
            (*prev).segment_queue_link.next = next;
        }
        if next.is_null() {
            self.tail = prev;
        } else {
            (*next).segment_queue_link.prev = prev;
        }
    }
}
