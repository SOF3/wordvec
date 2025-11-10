use core::{hint::assert_unchecked, iter::FusedIterator, mem::{self, MaybeUninit}, ops::RangeBounds};

use crate::resolve_range;

pub(super) struct Retain<'a, T> {
    set_len:     super::LengthSetter<'a>,
    /// The slice of all initially initialized data.
    init_slice:  &'a mut [MaybeUninit<T>],
    /// Index of the next item to determine for extraction.
    read_len:    usize,
    /// Index of the next slot to write into.
    /// Must be less than or equal to `read_len`.
    written_len: usize,
    /// When `read_len >= stop_len`, the data are unconditionally retained.
    /// `stop_len` is guaranteed to be less than or equal to `init_slice.len()`.
    stop_len: usize,
}

impl<'a, T> Retain<'a, T> {
    pub(super) fn new<const N: usize>(vec: &'a mut super::WordVec<T, N>, range: impl RangeBounds<usize>) -> Self {
        let (capacity_slice, old_len, mut set_len) = vec.as_uninit_slice_with_length_setter();
        let (start, end) = resolve_range(range, old_len);

        // SAFETY: length 0 is always safe
        unsafe { set_len.set_len(start) };

        Self { set_len, init_slice: &mut capacity_slice[..old_len], read_len: start, written_len: start, stop_len: end }
    }
}

impl<T> Drop for Retain<'_, T> {
    fn drop(&mut self) {
        // Shift all unvisited elements forward.
        let data_len = self.init_slice.len();
        let data_ptr = self.init_slice.as_mut_ptr();
        let moved_len = data_len - self.read_len;
        unsafe {
            core::ptr::copy(data_ptr.add(self.read_len), data_ptr.add(self.written_len), moved_len);
        }

        // SAFETY: ensured by target_len setters
        unsafe {
            self.set_len.set_len(self.written_len + moved_len);
        }
    }
}

impl<T> Retain<'_, T> {
    pub(super) fn next(&mut self, should_retain: impl FnOnce(&mut T) -> bool) -> NextResult<T> {
        // SAFETY: guaranteed by data structure contract.
        unsafe { assert_unchecked(self.stop_len <= self.init_slice.len()) };

        if self.read_len >= self.stop_len {
            // The remaining items will be shifted forward when self is dropped.
            return NextResult::Exhausted;
        }

        let Some(item_uninit) = self.init_slice.get_mut(self.read_len) else {
            return NextResult::Exhausted;
        };

        // SAFETY: init_slice[read_len..] are always initialized
        let item_mut = unsafe { item_uninit.assume_init_mut() };

        // If `should_retain` panics, `item` is no longer referenced,
        // so the state of this struct is just as if the current `next` call never happened.
        // Thus the destructor will work as expected.
        let retain = should_retain(item_mut);

        if retain {
            let src_index = self.read_len;
            let dest_index = self.written_len;

            // init_slice[read_len] is moved to init_slice[written_len] after this step.
            // If read_len == written_len, this just retains the item in place
            // and has no safety implications.
            // If read_len != written_len, by contract read_len > written_len,
            // so init_slice[written_len..read_len] is uninitialized,
            // and after this operation, init_slice[written_len] becomes initialized
            // while init_slice[read_len] becomes uninitialized.
            self.read_len += 1;
            self.written_len += 1;

            if src_index != dest_index {
                unsafe {
                    // SAFETY: read_len != written_len checked in condition
                    let [src, dest] =
                        self.init_slice.get_disjoint_unchecked_mut([src_index, dest_index]);
                    dest.write(mem::replace(src, MaybeUninit::uninit()).assume_init());
                }
            }
            // If src_index == dest_index, this move would be a no-op

            NextResult::Retained
        } else {
            // this never overflows because read_len < init_slice.len() <= usize::MAX
            self.read_len += 1;

            // SAFETY: item can be safely moved out as an initialized value.
            let item = mem::replace(item_uninit, MaybeUninit::uninit());
            let item = unsafe { item.assume_init() };

            NextResult::Removed(item)
        }
    }
}

pub(super) enum NextResult<T> {
    Exhausted,
    Retained,
    Removed(T),
}

pub(super) struct ExtractIf<'a, T, F> {
    pub(super) retain:        Retain<'a, T>,
    pub(super) should_remove: F,
}

impl<T, F> Iterator for ExtractIf<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return match self.retain.next(|elem| !(self.should_remove)(elem)) {
                NextResult::Exhausted => None,
                NextResult::Retained => continue,
                NextResult::Removed(item) => Some(item),
            };
        }
    }
}

impl<T, F> FusedIterator for ExtractIf<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{}
