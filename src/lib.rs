//! A [thin][thinvec] and [small][smallvec] vector
//! that can fit data into a single `usize`.
//!
//! See [the readme on GitHub][git-repo]
//! for detailed explanation of the memory layout.
//!
//! ## When to use
//!
//! Although the technical limit is `N <= 127`,
//! it is not meaningful to set `N` such that `align_of::<T>() + N * size_of::<T>()` exceeds 24;
//! `WordVec` has no advantage over [`SmallVec`][smallvec] if it cannot pack into a smaller struct.
//!
//! Thin vectors are significantly (several times) slower than conventional vectors
//! since reading the length and capacity usually involves accessing memory out of active cache.
//! Thus, heap layout is supposed to be the cold path.
//! In other words, `WordVec` is basically
//! "length should never exceed `N`, but behavior is still correct when it exceeds".
//!
//! Since the length encoding in the inlined layout is indirect (involves a bitshift),
//! raw inlined access also tends to be slower in `WordVec` compared to `SmallVec`,
//! as a tradeoff of reduced memory footprint of each vector alone.
//! This may get handy in scenarios with a large array of small vectors,
//! e.g. as an ECS component.
//!
//! [thinvec]: https://docs.rs/thin-vec
//! [smallvec]: https://docs.rs/smallvec
//! [git-repo]: https://github.com/SOF3/wordvec

#![no_std]
#![warn(clippy::pedantic)]

extern crate alloc;

use alloc::alloc::{alloc, dealloc, handle_alloc_error, realloc};
use core::alloc::Layout;
use core::hash::{self, Hash};
use core::hint::assert_unchecked;
use core::iter::FusedIterator;
use core::mem::{ManuallyDrop, MaybeUninit, needs_drop};
use core::ops::{self, Deref, DerefMut};
use core::ptr::{self, NonNull};
use core::{array, cmp, fmt, iter, slice};

#[cfg(test)]
mod tests;

mod polyfill;
#[allow(clippy::wildcard_imports)]
use polyfill::*;

/// A thin and small vector that can fit data into a single `usize`.
///
/// `N` must be less than or equal to 127.
/// It is advised that `size_of::<T>() * N + align_of::<T>()` does not exceed 20 bytes.
///
/// See the [readme](https://github.com/SOF3/wordvec) for more information.
pub struct WordVec<T, const N: usize>(Inner<T, N>);

union Inner<T, const N: usize> {
    small: ManuallyDrop<Small<T, N>>,
    large: ManuallyDrop<Large<T>>,
}

impl<T, const N: usize> Inner<T, N> {
    const fn assert_generics() {
        const {
            assert!(N <= 127, "N must be less than or equal to 127 to fit in the marker byte");
            assert!(align_of::<usize>() >= 2, "usize must be aligned to 2 bytes");
        }
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

    /// This function never reads or writes `Allocated.len`.
    /// This allows the local cache of `len` in `extend_large_iter`
    /// to remain valid when reallocation occurs during growth.
    fn grow(&mut self, min_new_cap: usize) -> usize {
        let mut new_cap = min_new_cap;

        let old_cap = self.as_allocated().0.cap;
        if let Some(double) = old_cap.checked_mul(2) {
            new_cap = new_cap.max(double);
        }

        self.grow_exact(new_cap);
        new_cap
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
            ptr.write(Allocated::<T> { cap, len: 0, data_start: [] });
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
    len:        usize,
    cap:        usize,
    data_start: [T; 0], // alignment of T, without the size of T.
}

impl<T> Allocated<T> {
    /// Extend the length of this allocation with the new data.
    ///
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - `(*this)` must be deref-able to a valid `&mut Self`.
    /// - `(*this).len + src.len() <= self.cap`
    /// - `src` is invalid after this function returns.
    /// - `src` must not be derived from `self`.
    unsafe fn extend(mut this: NonNull<Self>, src: *mut [T]) {
        let len = unsafe {
            let this_mut = this.as_mut();
            let old_len = this_mut.len;
            this_mut.len = old_len + src.len();
            old_len
        };
        unsafe {
            Self::extend_data(this, src, len);
        }
    }

    /// Like `extend`, but reads the length from a parameter and does not write the new length.
    unsafe fn extend_data(this: NonNull<Self>, src: *mut [T], old_len: usize) {
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
        unsafe { (&raw mut (*this.as_ptr()).data_start).cast() }
    }
}

impl<T, const N: usize> WordVec<T, N> {
    /// Creates an empty vector.
    #[must_use]
    pub fn new() -> Self { Self::default() }

    /// Returns an immutable slice of all initialized data.
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

    /// Returns a mutable slice of all initialized data.
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

    /// Returns the full capacity of the allocated buffer, which may be partly uninitialized,
    /// along with the length of the initialized portion.
    ///
    /// This is equivalent to `(slice_from_raw_parts(as_mut_ptr(), cap), len)`.
    pub fn as_uninit_slice_with_length(&mut self) -> (&mut [MaybeUninit<T>], usize) {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: variant indicated by marker
                let small = unsafe { &mut self.0.small };
                (&mut small.data[..], usize::from(len))
            }
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &mut self.0.large };
                // SAFETY: Large.0 is always a valid reference.
                let (allocated, data_start) = large.as_allocated_mut();
                // SAFETY: `allocated.data` is always a valid *uninit* slice pointer of length `allocated.cap`
                let slice = unsafe {
                    slice::from_raw_parts_mut(data_start.cast::<MaybeUninit<T>>(), allocated.cap)
                };
                (slice, allocated.len)
            }
        }
    }

    /// Returns the number of items in this vector.
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

    /// Returns whether the vector is empty.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns the capacity of this vector.
    ///
    /// Capacity is always `N` when the inlined layout is used.
    /// When the heap layout is used, `capacity` returns the maximum number of items
    /// that can be stored in this vector without reallocating.
    ///
    /// Capacity only grows when length exceeds the current capacity,
    /// so `capacity()` is never less than `N`.
    /// Nevertheless, the length may shrink without reducing capacity,
    /// so `len() <= N` does **not** imply `capacity() == N`.
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

    /// Pushes an item to the end of this vector.
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
                // SAFETY: we have moved to large right above.
                unsafe { self.extend_large_slice(&mut *values) }
            }
            ParsedMarker::Large => {
                let mut values = ManuallyDrop::new([value]);
                // SAFETY: marker is Large
                unsafe { self.extend_large_slice(&mut *values) }
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
    /// The current marker must be `small` (which will not overflow `u8`).
    ///
    /// # Panics
    /// Panics if `values` yields more than `N - self.len()` items.
    unsafe fn extend_small_iter(&mut self, values: impl Iterator<Item = T>) {
        // SAFETY: function safety invariant
        let small = unsafe { &mut self.0.small };

        let current_len = usize::from(small.marker >> 1);

        for (i, value) in values.enumerate() {
            let dest = small.data.get_mut(current_len + i).expect("values has too many items");
            dest.write(value);
            small.marker += 2; // this will not overflow since length <= N <= 127
        }
    }

    /// # Safety
    /// - The current marker must be `large`.
    /// - `values` has the same invariants as [`ptr::drop_in_place`].
    unsafe fn extend_large_slice(&mut self, values: *mut [T]) {
        // SAFETY: function safety invariant
        let large = unsafe { &mut self.0.large };
        let (&Allocated { len, cap, .. }, _) = large.as_allocated();
        let new_len = len.checked_add(values.len()).expect("new length is out of bounds");
        if new_len > cap {
            large.grow(new_len);
        }

        unsafe {
            Allocated::extend(large.0, values);
        }
    }

    /// # Safety
    /// The current marker must be `large`.
    unsafe fn extend_large_iter(&mut self, values: impl Iterator<Item = T>) {
        // SAFETY: function safety invariant
        let large = unsafe { &mut self.0.large };
        let (&Allocated { len, mut cap, .. }, _) = large.as_allocated();

        let (hint_min, _) = values.size_hint();
        let hint_len = len.checked_add(hint_min).expect("new length out of bounds");

        if hint_len > cap {
            cap = large.grow(hint_len);
        }

        let mut new_len = len;
        let mut values = values.fuse();

        while new_len < cap {
            // This simple loop allows better optimizations subject to the implementation of
            // `values`.
            if let Some(item) = values.next() {
                new_len += 1; // new_len < cap <= usize::MAX, so this will not overflow
                unsafe {
                    let dest = Allocated::<T>::data_start(large.0).add(new_len - 1);
                    dest.write(item);
                }
            } else {
                // capacity is not full but input is exhausted
                break;
            }
        }

        for item in values {
            new_len = new_len.checked_add(1).expect("new length is out of bounds");
            if new_len > cap {
                cap = large.grow(new_len);
            }

            unsafe {
                let dest = Allocated::<T>::data_start(large.0).add(new_len - 1);
                dest.write(item);
            }
        }

        // SAFETY:
        // - large will remain large
        // - large.0 might have been reallocated, but accessing it through `self` is still correct.
        // - only one item pushed at a time
        unsafe {
            let mut allocated_ptr = self.0.large.0;
            allocated_ptr.as_mut().len = new_len;
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

    /// Removes the item at index `index`,
    /// shifting all subsequent items forward.
    ///
    /// This is an O(n) operation.
    ///
    /// # Panics
    /// Panics if `index >= self.len()`.
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        match self.try_remove(index) {
            Some(v) => v,
            None => panic!("Cannot remove index {index} from length {}", self.len()),
        }
    }

    /// Like [`remove`](Self::remove),
    /// but returns `None` instead of panicking if `index` is out of bounds.
    #[inline]
    pub fn try_remove(&mut self, index: usize) -> Option<T> {
        let slice = self.remove_last_uninit(index)?;

        let mutated_slice = &mut slice[index..];
        mutated_slice.rotate_left(1);
        // SAFETY: index < `old_len`, so `mutated_slice` must not be empty.
        unsafe { Some(mutated_slice.last_mut().unwrap_unchecked().assume_init_read()) }
    }

    /// Removes the item at index `index`,
    /// moving the last item behind (if any) to its original position.
    ///
    /// This is an O(1) operation and changes the order.
    ///
    /// # Panics
    /// Panics if `index >= self.len()`.
    pub fn swap_remove(&mut self, index: usize) -> T {
        match self.try_swap_remove(index) {
            Some(v) => v,
            None => panic!("Cannot remove index {index} from length {}", self.len()),
        }
    }

    /// Like [`swap_remove`](Self::swap_remove),
    /// but returns `None` instead of panicking if `index` is out of bounds.
    pub fn try_swap_remove(&mut self, index: usize) -> Option<T> {
        let slice = self.remove_last_uninit(index)?;

        // SAFETY: slice[index] and slice.last() were previously initialized.
        // Whichever item ends up at the latter position will no longer be reachable.
        unsafe {
            slice.swap(index, slice.len() - 1);
            Some(slice.last_mut().unwrap_unchecked().assume_init_read())
        }
    }

    /// Reduces the length by one.
    /// Returns `None` if the vector length is less than or equal to `len_gt`.
    ///
    /// `len_gt` is effectively the minimum new length after this function returns.
    ///
    /// This method cannot cause UB, but it will leak memory
    /// if the last item in the returned slice is not dropped.
    ///
    /// Returns the *original* initialized slice before removing the last item.
    fn remove_last_uninit(&mut self, len_gt: usize) -> Option<&mut [MaybeUninit<T>]> {
        match self.0.parse_marker() {
            ParsedMarker::Small(old_len) => {
                // SAFETY: marker is Small
                let small = unsafe { &mut self.0.small };

                if usize::from(old_len) <= len_gt {
                    return None;
                }

                // SAFETY: since new_len <= self.len <= 127, (new_len << 1) is still within bounds of u8.
                small.marker = unsafe { small.marker.unchecked_sub(2) };

                Some(&mut small.data[..usize::from(old_len)])
            }
            ParsedMarker::Large => {
                // SAFETY: marker is Large
                let large = unsafe { &mut self.0.large };
                let (allocated, data_start) = large.as_allocated_mut();

                let old_len = allocated.len;
                if old_len <= len_gt {
                    return None;
                }

                let new_len = old_len - 1; // this never overflows since `old_len > len_gt >= 0`
                allocated.len = new_len;

                // SAFETY: `allocated.data` is always a valid *uninit* slice pointer of length `allocated.cap`
                let slice = unsafe {
                    slice::from_raw_parts_mut(data_start.cast::<MaybeUninit<T>>(), old_len)
                };
                Some(slice)
            }
        }
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

impl<T, const N: usize> Extend<T> for WordVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let mut iter = iter.into_iter();
        let hint_min = iter.size_hint().0;

        match self.0.parse_marker() {
            ParsedMarker::Small(len) if usize::from(len) + hint_min <= N => {
                // SAFETY: marker is Small
                unsafe {
                    self.extend_small_iter(iter.by_ref().take(N - usize::from(len)));
                }

                let mut peekable = iter.peekable();
                if peekable.peek().is_some() {
                    // The iterator has more items than `hint_min`.
                    // We don't know how many more we will get, so our best bet is to double it.
                    unsafe {
                        self.move_small_to_large(N * 2);
                    }
                    // SAFETY: we have moved to large right above.
                    unsafe { self.extend_large_iter(peekable) }
                }
            }
            ParsedMarker::Small(len) => {
                unsafe {
                    self.move_small_to_large(usize::from(len) + hint_min);
                }
                // SAFETY: we have moved to large right above.
                unsafe { self.extend_large_iter(iter) }
            }
            ParsedMarker::Large => {
                // SAFETY: marker is Large
                unsafe { self.extend_large_iter(iter) }
            }
        }
    }
}

impl<T, const N: usize> FromIterator<T> for WordVec<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::default();
        v.extend(iter);
        v
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for WordVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self.as_slice(), f) }
}

impl<T, const N: usize> Deref for WordVec<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] { self.as_slice() }
}

impl<T, const N: usize> DerefMut for WordVec<T, N> {
    fn deref_mut(&mut self) -> &mut [T] { self.as_mut_slice() }
}

impl<T, const N: usize, Idx> ops::Index<Idx> for WordVec<T, N>
where
    [T]: ops::Index<Idx>,
{
    type Output = <[T] as ops::Index<Idx>>::Output;

    fn index(&self, index: Idx) -> &Self::Output { self.as_slice().index(index) }
}

impl<T, const N: usize, Idx> ops::IndexMut<Idx> for WordVec<T, N>
where
    [T]: ops::IndexMut<Idx>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T: PartialEq, const N: usize> PartialEq for WordVec<T, N> {
    fn eq(&self, other: &Self) -> bool { self.as_slice() == other.as_slice() }
}

impl<T: Eq, const N: usize> Eq for WordVec<T, N> {}

impl<T: PartialOrd, const N: usize> PartialOrd for WordVec<T, N> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, const N: usize> Ord for WordVec<T, N> {
    fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_slice().cmp(other.as_slice()) }
}

impl<T: Hash, const N: usize> Hash for WordVec<T, N> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) { self.as_slice().hash(state); }
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

/// Implements [`IntoIterator`] for [`WordVec`].
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
