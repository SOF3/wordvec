//! Traits trivially implemented by delegation.

use alloc::alloc::Global;
use core::alloc::Allocator;
use core::borrow::{Borrow, BorrowMut};
use core::hash::{self, Hash};
use core::ops::{Deref, DerefMut};
use core::{cmp, fmt, ops, slice};

use crate::WordVec;

impl<T, const N: usize> Default for WordVec<T, N, Global> {
    fn default() -> Self { Self::new() }
}

impl<T, const N: usize> FromIterator<T> for WordVec<T, N, Global> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::default();
        v.extend(iter);
        v
    }
}

impl<T: fmt::Debug, const N: usize, A: Allocator> fmt::Debug for WordVec<T, N, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self.as_slice(), f) }
}

impl<T, const N: usize, A: Allocator> Deref for WordVec<T, N, A> {
    type Target = [T];

    fn deref(&self) -> &[T] { self.as_slice() }
}

impl<T, const N: usize, A: Allocator> DerefMut for WordVec<T, N, A> {
    fn deref_mut(&mut self) -> &mut [T] { self.as_mut_slice() }
}

impl<T, const N: usize, A: Allocator> AsRef<[T]> for WordVec<T, N, A> {
    fn as_ref(&self) -> &[T] { self.as_slice() }
}

impl<T, const N: usize, A: Allocator> AsMut<[T]> for WordVec<T, N, A> {
    fn as_mut(&mut self) -> &mut [T] { self.as_mut_slice() }
}

impl<T, const N: usize, A: Allocator> Borrow<[T]> for WordVec<T, N, A> {
    fn borrow(&self) -> &[T] { self.as_slice() }
}

impl<T, const N: usize, A: Allocator> BorrowMut<[T]> for WordVec<T, N, A> {
    fn borrow_mut(&mut self) -> &mut [T] { self.as_mut_slice() }
}

impl<T, const N: usize, Idx, A: Allocator> ops::Index<Idx> for WordVec<T, N, A>
where
    [T]: ops::Index<Idx>,
{
    type Output = <[T] as ops::Index<Idx>>::Output;

    fn index(&self, index: Idx) -> &Self::Output { self.as_slice().index(index) }
}

impl<T, const N: usize, Idx, A: Allocator> ops::IndexMut<Idx> for WordVec<T, N, A>
where
    [T]: ops::IndexMut<Idx>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T: PartialEq, const N: usize, A: Allocator> PartialEq for WordVec<T, N, A> {
    fn eq(&self, other: &Self) -> bool { self.as_slice() == other.as_slice() }
}

impl<T: Eq, const N: usize, A: Allocator> Eq for WordVec<T, N, A> {}

impl<T: PartialOrd, const N: usize, A: Allocator> PartialOrd for WordVec<T, N, A> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, const N: usize, A: Allocator> Ord for WordVec<T, N, A> {
    fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_slice().cmp(other.as_slice()) }
}

impl<T: Hash, const N: usize, A: Allocator> Hash for WordVec<T, N, A> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) { self.as_slice().hash(state); }
}

impl<'a, T, const N: usize, A: Allocator> IntoIterator for &'a WordVec<T, N, A> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter { self.as_slice().iter() }
}

impl<'a, T, const N: usize, A: Allocator> IntoIterator for &'a mut WordVec<T, N, A> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter { self.as_mut_slice().iter_mut() }
}
