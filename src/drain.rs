use alloc::slice;
use core::iter::{self, FusedIterator};
use core::mem::MaybeUninit;

/// Return value of [`WordVec::drain`](super::WordVec::drain).
pub struct Drain<'a, T> {
    pub(super) drained: slice::IterMut<'a, MaybeUninit<T>>,
}

impl<'a, T> Drain<'a, T> {
    fn as_inited(
        &mut self,
    ) -> iter::Map<&mut slice::IterMut<'a, MaybeUninit<T>>, impl Fn(&mut MaybeUninit<T>) -> T> {
        // HACK: this function is actually unsafe.
        // But if we write this as a closure instead, RPIT would have type inference issues.
        fn unsafe_assume_init_read<T>(item: &mut MaybeUninit<T>) -> T {
            // SAFETY: each item is only `assume_init_read` once.
            // Iterator does not know how to copy a `&mut`.
            unsafe { item.assume_init_read() }
        }

        self.drained.by_ref().map(unsafe_assume_init_read::<T>)
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> { self.as_inited().next() }

    fn size_hint(&self) -> (usize, Option<usize>) { self.drained.size_hint() }

    fn count(self) -> usize {
        self.drained.len()
        // self.drained will be dropped here
    }

    fn nth(&mut self, n: usize) -> Option<T> { self.as_inited().nth(n) }

    // fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
    //     self.as_inited().advance_by(n)
    // }

    fn last(mut self) -> Option<T> { self.as_inited().last() }

    fn fold<B, F>(mut self, init: B, f: F) -> B
    where
        F: FnMut(B, T) -> B,
    {
        self.as_inited().fold(init, f)
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<T> { self.as_inited().next_back() }

    fn nth_back(&mut self, n: usize) -> Option<T> { self.as_inited().nth_back(n) }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    fn len(&self) -> usize { self.drained.len() }
}

impl<T> FusedIterator for Drain<'_, T> {}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) { self.as_inited().for_each(drop); }
}
