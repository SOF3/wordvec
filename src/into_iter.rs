use core::alloc::Allocator;
use core::array;
use core::iter::{self, FusedIterator};
use core::mem::{ManuallyDrop, MaybeUninit, needs_drop};
use core::ptr::{self, NonNull};

use crate::{Allocated, Large, ParsedMarker, WordVec};

impl<T, const N: usize, A: Allocator> IntoIterator for WordVec<T, N, A> {
    type Item = T;
    type IntoIter = IntoIter<T, N, A>;

    fn into_iter(self) -> Self::IntoIter {
        let (mut inner, alloc) = {
            // Destructure into parts. The real destructor is called by `IntoIter`.
            let this = ManuallyDrop::new(self);
            unsafe { (ptr::read(&raw const this.inner), ptr::read(&raw const this.alloc)) }
        };
        match inner.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: indicated by marker
                let small = unsafe { ManuallyDrop::take(&mut inner.small) };
                let data = small.data;
                let valid = data.into_iter().take(len.into());
                IntoIter(IntoIterInner::Small(valid.into_iter()))
            }
            ParsedMarker::Large => {
                // SAFETY: indicated by marker
                let ptr = unsafe { inner.large.0 };
                IntoIter(IntoIterInner::Large { ptr, start: 0, alloc })
            }
        }
    }
}

/// Implements [`IntoIterator`] for [`WordVec`].
pub struct IntoIter<T, const N: usize, A: Allocator>(IntoIterInner<T, N, A>);

enum IntoIterInner<T, const N: usize, A: Allocator> {
    Small(iter::Take<array::IntoIter<MaybeUninit<T>, N>>),
    Large { ptr: NonNull<Allocated<T>>, start: usize, alloc: A },
}

impl<T, const N: usize, A: Allocator> Iterator for IntoIter<T, N, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IntoIterInner::Small(iter) => {
                // SAFETY: only initialized values are taken
                iter.next().map(|uninit| unsafe { uninit.assume_init() })
            }
            IntoIterInner::Large { ptr: alloc, start, alloc: _ } => {
                // SAFETY: the header is always valid before drop.
                let len = unsafe { alloc.as_mut() }.len;

                let index = *start;
                if index >= len {
                    return None;
                }
                *start = index + 1;

                let value = unsafe { Allocated::data_start(*alloc) };
                // SAFETY: index was not consumed before this function was called.
                let value = unsafe { ptr::read(value.add(index)) };
                Some(value)
            }
        }
    }
}

// Small: array::IntoIter implements FusedIterator.
// Large: we check `index >= len` before incrementing (not doing so may lead to UB caused by
// overflow).
impl<T, const N: usize, A: Allocator> FusedIterator for IntoIter<T, N, A> {}

impl<T, const N: usize, A: Allocator> Drop for IntoIter<T, N, A> {
    fn drop(&mut self) {
        match &mut self.0 {
            IntoIterInner::Small(iter) => {
                // SAFETY: only initialized values are taken
                iter.by_ref().for_each(|uninit| drop(unsafe { uninit.assume_init() }));
            }
            IntoIterInner::Large { ptr, start, alloc } => {
                // SAFETY: the header is always valid before drop.
                let &mut Allocated { len, cap, .. } = unsafe { ptr.as_mut() };

                if needs_drop::<T>() {
                    let value = unsafe { Allocated::data_start(*ptr) };
                    // SAFETY: `start` <= `len`.
                    let start_ptr = unsafe { value.add(*start) };
                    // SAFETY: All items in the range start..len are still initialized and need
                    // dropping.
                    unsafe {
                        let to_drop = ptr::slice_from_raw_parts_mut(start_ptr, len - *start);
                        ptr::drop_in_place(to_drop);
                    }
                }

                let layout = Large::<T>::new_layout(cap);
                // SAFETY: alloc is valid before dropped; layout is provided by the header itself.
                unsafe {
                    alloc.deallocate(ptr.cast(), layout);
                }
            }
        }
    }
}
