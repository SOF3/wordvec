#![no_std]

extern crate alloc;

use alloc::alloc::{alloc, dealloc, handle_alloc_error, realloc};
use core::alloc::Layout;
use core::hint::assert_unchecked;
use core::iter::FusedIterator;
use core::mem::{ManuallyDrop, MaybeUninit, needs_drop};
use core::ptr::{self, NonNull};
use core::{array, iter, slice};

#[cfg(test)]
mod tests;

mod polyfill;
use polyfill::*;

pub struct WordVec<T, const N: usize>(Inner<T, N>);

union Inner<T, const N: usize> {
    small: ManuallyDrop<Small<T, N>>,
    large: ManuallyDrop<Large<T>>,
}

impl<T, const N: usize> Inner<T, N> {
    const fn assert_generics() {
        assert!(N <= 127, "N must be less than or equal to 127 to fit in the marker byte");
        assert!(align_of::<usize>() >= 2, "usize must be aligned to 2 bytes");
    }

    fn parse_marker(&self) -> ParsedMarker {
        Self::assert_generics();

        let marker = unsafe {
            // SAFETY: the LSB is always initialized in both variants.
            self.small.marker
        };
        if marker % 2 == 0 {
            ParsedMarker::Large
        } else {
            let len = marker >> 1;

            // SAFETY: invariant of `Small` when it is actually small.
            unsafe {
                assert_unchecked(usize::from(len) <= N);
            }

            ParsedMarker::Small(len)
        }
    }
}

#[cfg(target_endian = "little")]
#[repr(C)]
struct Small<T, const N: usize> {
    marker: u8,
    data:   [MaybeUninit<T>; N],
}

#[cfg(target_endian = "big")]
compile_error!("Big-endian targets are not supported yet");

enum ParsedMarker {
    Small(u8),
    Large,
}

struct Large<T>(NonNull<Allocated<T>>);

impl<T> Large<T> {
    fn new_layout(cap: usize) -> Layout {
        let additional_size = size_of::<T>().checked_mul(cap).expect("new capacity is too large");
        let size = size_of::<Allocated<T>>()
            .checked_add(additional_size)
            .expect("new capacity is too large");
        let align = align_of::<Allocated<T>>();
        // SAFETY: size of Allocated<T> must be a multiple of align of Allocated<T>,
        // which must be a multiple of align of T due to the `data` field.
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }

    fn as_allocated(&self) -> (&Allocated<T>, *const T) {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        unsafe { (self.0.as_ref(), Allocated::data_start(self.0)) }
    }

    fn as_allocated_mut(&mut self) -> (&mut Allocated<T>, *mut T) {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        // The `data_start` pointer does not alias the `&mut Allocated`
        // since `Allocated` only contains an empty array.
        unsafe { (self.0.as_mut(), Allocated::data_start(self.0)) }
    }

    fn current_layout(&self) -> Layout {
        let cap = self.as_allocated().0.cap;
        Self::new_layout(cap)
    }

    fn grow(&mut self, min_new_cap: usize) {
        let mut new_cap = min_new_cap;

        let old_cap = self.as_allocated().0.cap;
        if let Some(double) = old_cap.checked_mul(2) {
            new_cap = new_cap.max(double);
        }

        self.grow_exact(new_cap);
    }

    fn grow_exact(&mut self, new_cap: usize) {
        let old_layout = self.current_layout();
        let new_layout = Self::new_layout(new_cap);
        // SAFETY: new_layout never returns a zero layout.
        let new_ptr = unsafe { realloc(self.0.as_ptr().cast(), old_layout, new_layout.size()) };
        let Some(new_ptr) = NonNull::new(new_ptr) else { handle_alloc_error(new_layout) };
        self.0 = new_ptr.cast();
        // SAFETY: the previous `cap` value was initialized to a valid value.
        unsafe {
            (*self.0.as_ptr()).cap = new_cap;
        }
    }

    /// Create a new `Large` and move the data from `src` to `dest`.
    ///
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - The data behind `src` is invalid after this function returns.
    unsafe fn new(cap: usize, src: *mut [T]) -> Self {
        let layout = Self::new_layout(cap);

        // SAFETY: new_layout never returns a zero layout.
        let ptr = unsafe { alloc(layout) };
        let Some(ptr) = NonNull::new(ptr) else { handle_alloc_error(layout) };
        let ptr = ptr.cast::<Allocated<T>>();

        // SAFETY: `ptr` can be derefed as an `Allocated<T>` since it was just allocated as such.
        unsafe {
            ptr.write(Allocated::<T> { cap, len: 0, _data_start: [] });
        }

        // SAFETY: The underlying `Allocated` is now initialized with the correct length and
        // capacity.
        unsafe {
            Allocated::extend(ptr, src);
        }

        Self(ptr)
    }
}

/// This struct only contains the header (and padding) of the heap allocation.
/// Due to provenance, `_data_start` cannot be directly converted to a slice reference;
/// the slice must always be derived from the allocation pointer (`NonNull<Allocated<T>>`)
/// directly.
#[repr(C)]
struct Allocated<T> {
    len:         usize,
    cap:         usize,
    _data_start: [T; 0], // alignment of T, without the size of T.
}

impl<T> Allocated<T> {
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - `(*this)` must be deref-able to a valid `&mut Self`.
    /// - `(*this).len + src.len() <= self.cap`
    /// - `src` is invalid after this function returns.
    /// - `src` must not be derived from `self`.
    unsafe fn extend(mut this: NonNull<Self>, src: *mut [T]) {
        let old_len = unsafe { this.as_ref() }.len;
        unsafe { this.as_mut() }.len += src.len();

        // SAFETY: length of self.data == self.cap >= new self.len >= old_len
        let dest_start = unsafe { Self::data_start(this).add(old_len) };

        // SAFETY: function safety invariant.
        unsafe {
            let src_start = src.cast::<T>();
            ptr::copy_nonoverlapping(src_start, dest_start, src.len());
        }
    }

    /// # Safety
    /// `this` must point to a valid header.
    ///
    /// The data behind the header are allowed to be uninitialized.
    unsafe fn data_start(this: NonNull<Self>) -> *mut T {
        unsafe { (&raw mut (*this.as_ptr())._data_start).cast() }
    }
}

impl<T, const N: usize> WordVec<T, N> {
    pub fn new() -> Self { Self::default() }

    pub fn as_slice(&self) -> &[T] {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: variant indicated by marker
                let small = unsafe { &self.0.small };
                // SAFETY: len must be less than or equal to N
                let uninit_slice = unsafe { small.data.get_unchecked(..usize::from(len)) };
                // SAFETY: marker indicates that all first `len` elements are initialized.
                unsafe { slice_assume_init_ref::<T>(uninit_slice) }
            }
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &self.0.large };
                // SAFETY: Large.0 is always a valid reference.
                let (allocated, data_start) = large.as_allocated();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`
                unsafe { slice::from_raw_parts(data_start, allocated.len) }
            }
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: variant indicated by marker
                let small = unsafe { &mut self.0.small };
                // SAFETY: len must be less than or equal to N
                let uninit_slice = unsafe { small.data.get_unchecked_mut(..usize::from(len)) };
                // SAFETY: marker indicates that all first `len` elements are initialized.
                unsafe { slice_assume_init_mut::<T>(uninit_slice) }
            }
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &mut self.0.large };
                // SAFETY: Large.0 is always a valid reference.
                let (allocated, data_start) = large.as_allocated_mut();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`
                unsafe { slice::from_raw_parts_mut(data_start, allocated.len) }
            }
        }
    }

    pub fn len(&self) -> usize {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => usize::from(len),
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &self.0.large };
                large.as_allocated().0.len
            }
        }
    }

    pub fn is_empty(&self) -> bool { self.len() == 0 }

    pub fn capacity(&self) -> usize {
        match self.0.parse_marker() {
            ParsedMarker::Small(_) => N,
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &self.0.large };
                large.as_allocated().0.cap
            }
        }
    }

    pub fn push(&mut self, value: T) {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) if usize::from(len) < N => {
                let mut values = ManuallyDrop::new([value]);
                // SAFETY: marker is Small
                unsafe { self.extend_small(&mut *values) }
            }
            ParsedMarker::Small(_) => {
                unsafe {
                    self.move_small_to_large(N + 1);
                }
                let mut values = ManuallyDrop::new([value]);
                // SAFETY: marker is Small
                unsafe { self.extend_large(&mut *values) }
            }
            ParsedMarker::Large => {
                let mut values = ManuallyDrop::new([value]);
                // SAFETY: marker is Small
                unsafe { self.extend_large(&mut *values) }
            }
        }
    }

    /// # Safety
    /// - The current marker must be `small`
    /// - `self.len() + values.len()` must be less than or equal to `N`
    ///   (which will not overflow `u8`).
    /// - `values` has the same invariants as [`ptr::drop_in_place`].
    unsafe fn extend_small(&mut self, values: *mut [T]) {
        debug_assert!(self.len() + values.len() <= N); // safety invariant check

        // SAFETY: function safety invariant
        let small = unsafe { &mut self.0.small };

        let current_len = usize::from(small.marker >> 1);
        let slice = &mut small.data.as_mut_slice()[current_len..current_len + values.len()];
        // SAFETY: `values` cannot overlap with `self` which is referenced mutably.
        unsafe {
            ptr::copy_nonoverlapping(
                values.cast::<T>(),
                slice.as_mut_ptr().cast::<T>(),
                values.len(),
            );
        }

        let new_len = (small.marker >> 1) + u8::try_from(values.len()).unwrap();
        small.marker = (new_len << 1) | 1;
    }

    /// # Safety
    /// - The current marker must be `large`
    /// - `values` has the same invariants as [`ptr::drop_in_place`].
    unsafe fn extend_large(&mut self, values: *mut [T]) {
        // SAFETY: function safety invariant
        let large = unsafe { &mut self.0.large };
        let (&Allocated { len, cap, .. }, _) = large.as_allocated();
        let new_len = len.checked_add(values.len()).expect("new length is out of bounds");
        if new_len > cap {
            large.grow(new_len);

            // SAFETY: `large` has grown to at least `new_len`.
            unsafe {
                Allocated::extend(large.0, values);
            }
        } else {
            // SAFETY: checked in the condition.
            unsafe {
                Allocated::extend(large.0, values);
            }
        }
    }

    /// # Safety
    /// - The current marker must be `small`
    unsafe fn move_small_to_large(&mut self, new_cap: usize) {
        // SAFETY: function safety invariant
        let small = unsafe { &mut self.0.small };
        let data = small.data.as_mut_ptr().cast::<T>();
        let small_len = small.marker >> 1;
        let data_slice = ptr::slice_from_raw_parts_mut(data, small_len.into());

        let large = unsafe { Large::new(new_cap, data_slice) };

        self.0.large = ManuallyDrop::new(large);
    }
}

impl<T, const N: usize> Default for WordVec<T, N> {
    fn default() -> Self {
        Self(Inner {
            small: ManuallyDrop::new(Small {
                marker: 1,
                data:   [const { MaybeUninit::uninit() }; N],
            }),
        })
    }
}

impl<T, const LENGTH: usize, const N: usize> From<[T; LENGTH]> for WordVec<T, N> {
    fn from(value: [T; LENGTH]) -> Self {
        Inner::<T, N>::assert_generics();

        if LENGTH <= N {
            let mut data = [const { MaybeUninit::uninit() }; N];
            for (dest, src) in iter::zip(&mut data[..LENGTH], value) {
                dest.write(src);
            }

            Self(Inner {
                small: ManuallyDrop::new(Small {
                    marker: u8::try_from(LENGTH << 1).unwrap() | 1,
                    data,
                }),
            })
        } else {
            let mut value = ManuallyDrop::new(value);
            let large = unsafe { Large::new(LENGTH, &mut *value) };
            Self(Inner { large: ManuallyDrop::new(large) })
        }
    }
}

impl<T, const N: usize> Drop for WordVec<T, N> {
    fn drop(&mut self) {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: variant indicated by marker
                let small = unsafe { &mut self.0.small };
                // SAFETY: len must be less than or equal to N
                let uninit_slice = unsafe { small.data.get_unchecked_mut(..usize::from(len)) };
                // SAFETY: marker indicates that all first `len` elements are initialized.
                unsafe { slice_assume_init_drop::<T>(uninit_slice) };
            }
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &mut self.0.large };
                // SAFETY: Large.0 is always a valid reference.
                let (allocated, data_start) = large.as_allocated_mut();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`,
                // and the destructor is only called once from its owner.
                unsafe {
                    let slice_ptr = ptr::slice_from_raw_parts_mut(data_start, allocated.len);
                    slice_ptr.drop_in_place();
                };

                // SAFETY: everything is now cleaned up, the allocation will no longer be used.
                unsafe {
                    dealloc(large.0.as_ptr().cast(), large.current_layout());
                }
            }
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a WordVec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter { self.as_slice().iter() }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut WordVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter { self.as_mut_slice().iter_mut() }
}

impl<T, const N: usize> IntoIterator for WordVec<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let mut this = ManuallyDrop::new(self); // the real destructor is called by `IntoIter`.
        match this.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: indicated by marker
                let small = unsafe { ManuallyDrop::take(&mut this.0.small) };
                let data = small.data;
                let valid = data.into_iter().take(len.into());
                IntoIter(IntoIterInner::Small(valid.into_iter()))
            }
            ParsedMarker::Large => {
                // SAFETY: indicated by marker
                let alloc = unsafe { this.0.large.0 };
                IntoIter(IntoIterInner::Large { alloc, start: 0 })
            }
        }
    }
}

pub struct IntoIter<T, const N: usize>(IntoIterInner<T, N>);

enum IntoIterInner<T, const N: usize> {
    Small(iter::Take<array::IntoIter<MaybeUninit<T>, N>>),
    Large { alloc: NonNull<Allocated<T>>, start: usize },
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IntoIterInner::Small(iter) => {
                // SAFETY: only initialized values are taken
                iter.next().map(|uninit| unsafe { uninit.assume_init() })
            }
            IntoIterInner::Large { alloc, start } => {
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
impl<T, const N: usize> FusedIterator for IntoIter<T, N> {}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        match &mut self.0 {
            IntoIterInner::Small(iter) => {
                // SAFETY: only initialized values are taken
                iter.by_ref().for_each(|uninit| drop(unsafe { uninit.assume_init() }));
            }
            IntoIterInner::Large { alloc, start } => {
                // SAFETY: the header is always valid before drop.
                let &mut Allocated { len, cap, .. } = unsafe { alloc.as_mut() };

                if needs_drop::<T>() {
                    let value = unsafe { Allocated::data_start(*alloc) };
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
                    dealloc(alloc.as_ptr().cast(), layout);
                }
            }
        }
    }
}

// SAFETY: These are equivalent to the safety of `Vec<T>`.
unsafe impl<T: Send, const N: usize> Send for WordVec<T, N> {}
unsafe impl<T: Sync, const N: usize> Sync for WordVec<T, N> {}
