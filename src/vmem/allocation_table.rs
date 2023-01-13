use super::{segment_list::SegmentQueue, Bt, BtKind, NUM_HASH_BUCKETS};

#[derive(Debug)]
pub struct AllocationTable {
    len: usize,
    pub(super) buckets: [SegmentQueue; NUM_HASH_BUCKETS],
}

impl AllocationTable {
    pub const fn new() -> AllocationTable {
        Self {
            len: 0,
            buckets: [SegmentQueue::EMPTY; NUM_HASH_BUCKETS],
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the bucket for the specified `base`.
    fn bucket_for_base(&self, base: usize) -> &SegmentQueue {
        let hash = murmur(base);
        &self.buckets[hash & (NUM_HASH_BUCKETS - 1)]
    }

    /// Returns a mutable reference to the bucket for the specified `base`.
    fn bucket_for_base_mut(&mut self, base: usize) -> &mut SegmentQueue {
        let hash = murmur(base);
        &mut self.buckets[hash & (NUM_HASH_BUCKETS - 1)]
    }

    /// Insert a boundary tag into the allocation hash table
    pub(super) unsafe fn insert(&mut self, bt: *mut Bt) {
        self.bucket_for_base_mut((*bt).base).insert_head(bt);
        self.len += 1;
    }

    /// Remove a boundary tag from the allocation hash table
    pub(super) unsafe fn remove(&mut self, bt: *mut Bt) {
        self.bucket_for_base_mut((*bt).base).remove(bt);
        self.len -= 1;
    }

    /// Find a boundary tag in the hash table.
    ///
    /// If found, the boundary tag is *not* removed from the table.
    pub(super) fn find(&self, base: usize) -> Option<*mut Bt> {
        unsafe {
            let bucket = self.bucket_for_base(base);
            let mut bt = bucket.head;
            while !bt.is_null() {
                if (*bt).base == base && (*bt).kind != BtKind::Span {
                    return Some(bt);
                }
                bt = (*bt).segment_queue_link.next;
            }
            None
        }
    }
}

#[cfg(target_pointer_width = "64")]
#[allow(clippy::unreadable_literal)]
const fn murmur(mut key: usize) -> usize {
    key ^= key >> 33;
    key = key.wrapping_mul(0xff51afd7ed558ccd);
    key ^= key >> 33;
    key = key.wrapping_mul(0xc4ceb9fe1a85ec53);
    key ^= key >> 33;
    key
}
#[cfg(target_pointer_width = "32")]
const fn murmur(mut key: usize) -> usize {
    key ^= key >> 16;
    key = key.wrapping_mul(0x85ebca6b);
    key ^= key >> 13;
    key = key.wrapping_mul(0xc2b2ae35);
    key ^= key >> 16;
    key
}
