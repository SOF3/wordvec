use core::iter::FusedIterator;
use core::mem::MaybeUninit;
use core::ptr;

use crate::LengthSetter;
use crate::polyfill::slice_assume_init_drop;

/// Return value of [`WordVec::drain`](super::WordVec::drain).
pub struct Drain<'a, T> {
    // Immutable pointers.
    pub(super) mutated_slice: &'a mut [MaybeUninit<T>],
    pub(super) total_drained: usize,

    // Iteration state.
    pub(super) remain_start: usize,
    pub(super) remain_end:   usize,

    // Finalization utils.
    pub(super) set_len:      LengthSetter<'a>,
    pub(super) set_len_base: usize,
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.remain_start == self.remain_end {
            return None;
        }

        // invariant ensured by Iterator methods
        debug_assert!(self.remain_start < self.remain_end);

        let data =
            unsafe { self.mutated_slice.get_unchecked_mut(self.remain_start).assume_init_read() };
        self.remain_start += 1;

        Some(data)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize { self.len() }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<T> {
        if self.remain_start == self.remain_end {
            return None;
        }

        // invariant ensured by Iterator methods
        debug_assert!(self.remain_start < self.remain_end);

        self.remain_end -= 1; // this never underflows since 0 <= remain_start < remain_end
        let data =
            unsafe { self.mutated_slice.get_unchecked_mut(self.remain_end).assume_init_read() };

        Some(data)
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    fn len(&self) -> usize { self.remain_end - self.remain_start }
}

impl<T> FusedIterator for Drain<'_, T> {}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        // Drop the remaining elements in the drained slice,
        // then replace the entire mutated_slice to the eventual value.
        // Only increase length after all of the above are done,
        // in case the destructor of `T` panics.

        // SAFETY: the "remain" range is always initialized.
        unsafe {
            slice_assume_init_drop(&mut self.mutated_slice[self.remain_start..self.remain_end]);
        }

        let count = self.mutated_slice.len() - self.total_drained;
        // SAFETY: drain_width <= mutated_slice.len() ensured during construction.
        unsafe {
            let mutated_ptr = self.mutated_slice.as_mut_ptr();
            let src_ptr = mutated_ptr.add(self.total_drained);
            let dest_ptr = mutated_ptr;
            ptr::copy(src_ptr, dest_ptr, count);
        }

        unsafe {
            self.set_len.set_len(self.set_len_base + self.mutated_slice.len() - self.total_drained);
        }
    }
}
