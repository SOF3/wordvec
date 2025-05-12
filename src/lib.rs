#![no_std]

extern crate alloc;

use alloc::alloc::{alloc, handle_alloc_error, realloc};
use core::alloc::Layout;
use core::hint::assert_unchecked;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};
use core::{iter, slice};

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

    fn as_allocated(&self) -> &Allocated<T> {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        unsafe { self.0.as_ref() }
    }

    fn as_allocated_mut(&mut self) -> &mut Allocated<T> {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        unsafe { self.0.as_mut() }
    }

    fn current_layout(&self) -> Layout {
        let cap = self.as_allocated().cap;
        Self::new_layout(cap)
    }

    fn grow(&mut self, min_new_cap: usize) {
        let mut new_cap = min_new_cap;

        let old_cap = self.as_allocated().cap;
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
        let mut ptr = ptr.cast::<Allocated<T>>();

        // SAFETY: `ptr` can be derefed as an `Allocated<T>` since it was just allocated as such.
        unsafe {
            ptr.write(Allocated::<T> { cap, len: 0, data: [] });
        }

        // SAFETY: The underlying `Allocated` is now initialized with the correct length and
        // capacity.
        let allocated = unsafe { ptr.as_mut() };
        // SAFETY: function safety invariant.
        unsafe {
            allocated.extend(src);
        }

        Self(ptr)
    }
}

#[repr(C)]
struct Allocated<T> {
    len:  usize,
    cap:  usize,
    data: [T; 0], // alignment of T, without the size of T.
}

impl<T> Allocated<T> {
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - `self.len + src.len() <= self.cap`
    /// - `src` is invalid after this function returns.
    /// - `src` must not be derived from `self`.
    unsafe fn extend(&mut self, src: *mut [T]) {
        let old_len = self.len;
        self.len += src.len();

        // SAFETY: length of self.data == self.cap >= new self.len >= old_len
        let dest_start = unsafe {
            let data_start = self.data.as_mut_ptr();
            data_start.add(old_len)
        };

        // SAFETY: function safety invariant.
        unsafe {
            let src_start = src.cast::<T>();
            ptr::copy_nonoverlapping(src_start, dest_start, src.len());
        }
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
                let allocated = large.as_allocated();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`
                unsafe { slice::from_raw_parts(allocated.data.as_ptr(), allocated.len) }
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
                let allocated = large.as_allocated_mut();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`
                unsafe { slice::from_raw_parts_mut(allocated.data.as_mut_ptr(), allocated.len) }
            }
        }
    }

    pub fn len(&self) -> usize {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => usize::from(len),
            ParsedMarker::Large => {
                // SAFETY: variant indicated by marker
                let large = unsafe { &self.0.large };
                large.as_allocated().len
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
                large.as_allocated().cap
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
        let allocated = large.as_allocated_mut();
        let new_len = allocated.len.checked_add(values.len()).expect("new length is out of bounds");
        if new_len > allocated.cap {
            large.grow(new_len);

            // SAFETY: Large.0 is a new valid reference after growing.
            let allocated = large.as_allocated_mut();
            // SAFETY: `large` has grown to at least `new_len`.
            unsafe {
                allocated.extend(values);
            }
        } else {
            // SAFETY: checked in the condition.
            unsafe {
                allocated.extend(values);
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
                let allocated = large.as_allocated_mut();
                // SAFETY: `allocated.data` is always a valid slice pointer of length `allocated.len`,
                // and the destructor is only called once from its owner.
                unsafe {
                    let slice_ptr =
                        ptr::slice_from_raw_parts_mut(allocated.data.as_mut_ptr(), allocated.len);
                    slice_ptr.drop_in_place();
                };
            }
        }
    }
}
