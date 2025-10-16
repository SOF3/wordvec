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
#![deny(missing_docs)]

extern crate alloc;

use alloc::alloc::{alloc, dealloc, handle_alloc_error, realloc};
use core::alloc::Layout;
use core::hint::assert_unchecked;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Bound, RangeBounds};
use core::ptr::{self, NonNull};
use core::{iter, slice};

#[cfg(test)]
mod tests;

mod polyfill;
#[allow(
    clippy::wildcard_imports,
    reason = "polyfill only contains a small number of unambiguous functions"
)]
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

    /// Create a new `Large` with a new allocation,
    /// and move the data from `src` to the new allocation.
    ///
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - The data behind `src` is invalid after this function returns.
    unsafe fn new(cap: usize, src: *mut [T]) -> Self {
        let this = Self::new_empty(cap);

        // SAFETY: The underlying `Allocated` is now initialized with the correct capacity.
        unsafe {
            Allocated::extend(this.0, src);
        }

        this
    }

    /// Create a new `Large` with a new allocation and zero length.
    fn new_empty(cap: usize) -> Self {
        let layout = Self::new_layout(cap);

        // SAFETY: new_layout never returns a zero layout.
        let ptr = unsafe { alloc(layout) };
        let Some(ptr) = NonNull::new(ptr) else { handle_alloc_error(layout) };
        let ptr = ptr.cast::<Allocated<T>>();

        // SAFETY: `ptr` can be derefed as an `Allocated<T>` since it was just allocated as such.
        unsafe {
            ptr.write(Allocated::<T> { cap, len: 0, data_start: [] });
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
    /// - `src` must not be derived from `this`.
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

struct ReserveArgs {
    len: usize,
    cap: usize,
}

struct ShrinkToArgs {
    len: usize,
}

impl<T, const N: usize> WordVec<T, N> {
    /// Creates an empty vector.
    #[must_use]
    pub const fn new() -> Self {
        Inner::<T, N>::assert_generics();

        Self(Inner {
            small: ManuallyDrop::new(Small {
                marker: 1,
                data:   [const { MaybeUninit::uninit() }; N],
            }),
        })
    }

    /// Creates a new **inlined** vector with specified data.
    ///
    /// This function is semantically equivalent to `WordVec::from(array)`,
    /// but allows constness due to array.
    ///
    /// # Errors
    /// A *compile* error occurs if `LENGTH > N`.
    #[must_use]
    pub const fn new_inlined<const LENGTH: usize>(values: [T; LENGTH]) -> Self {
        const {
            Inner::<T, N>::assert_generics();
            assert!(LENGTH <= N, "new_inlined can only be used to create an inlined vector");
        }

        let mut data = [const { MaybeUninit::uninit() }; N];
        let mut index = 0;
        while index < LENGTH {
            // SAFETY: each index is only copied once, and `value` will no longer be used.
            let value = &values[index];
            unsafe { data[index].write(ptr::read(value)) };
            index += 1;
        }
        mem::forget(values); // do not drop values; they have already been moved

        #[expect(
            clippy::cast_possible_truncation,
            reason = "LENGTH <= N <= 127 must be within bounds of u7"
        )]
        Self(Inner {
            small: ManuallyDrop::new(Small { marker: const { (LENGTH << 1) as u8 } | 1, data }),
        })
    }

    /// Creates an empty vector with the specified capacity.
    ///
    /// The resultant capacity is actually `max(N, cap)`.
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Inner::<T, N>::assert_generics();

        if cap <= N {
            Self::default()
        } else {
            let large = Large::new_empty(cap);
            Self(Inner { large: ManuallyDrop::new(large) })
        }
    }

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

    /// Returns the full partially-initialized buffer with the length of the initialized portion,
    /// and a raw setter for the length.
    ///
    /// This is equivalent to `(slice_from_raw_parts(as_mut_ptr(), capacity), length, set_length)`,
    /// but with the correct provenance since `as_mut_ptr` only returns provenance up to `len`.
    ///
    /// # Safety
    /// Although it is safe to call this function,
    /// the returned types are only useful through unsafe APIs.
    ///
    /// For `let (slice, len, set_len) = v.as_uninit_slice_with_length_setter()`,
    /// - Initially, only `slice[..len]` are initialized.
    /// - `set_len.set_len(n)` must only be called when `slice[..n]` are *already* initialized.
    /// - `slice[k..n]` must not be deinitialized (e.g. `assume_init_drop`ped)
    ///   before calling `set_len.set_len(k)` if the current length is `n`.
    pub fn as_uninit_slice_with_length_setter(
        &mut self,
    ) -> (&mut [MaybeUninit<T>], usize, LengthSetter<'_>) {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                // SAFETY: variant indicated by marker
                let small = unsafe { &mut *self.0.small };
                (
                    &mut small.data[..],
                    usize::from(len),
                    LengthSetter {
                        inner:                             LengthSetterInner::Small(
                            &mut small.marker,
                        ),
                        #[cfg(debug_assertions)]
                        capacity:                          N,
                    },
                )
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
                (
                    slice,
                    allocated.len,
                    LengthSetter {
                        inner:                             LengthSetterInner::Large(
                            &mut allocated.len,
                        ),
                        #[cfg(debug_assertions)]
                        capacity:                          allocated.cap,
                    },
                )
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

    /// Inserts an item at the specified index.
    ///
    /// # Panics
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: T) {
        self.reserve(1);
        let (capacity_slice, len, mut set_len) = self.as_uninit_slice_with_length_setter();
        assert!(index <= len, "insertion index (is {index}) should be <= len (is {len})");

        #[expect(clippy::range_plus_one, reason = "len+1 is more explicit")]
        let mutated_slice = &mut capacity_slice[index..len + 1];

        // mutated_slice[..mutated_slice.len() - 1] is initialized and
        // needs to be right-shifted to `mutated_slice[1..]`
        let mutated_len = mutated_slice.len();
        if !mutated_slice.is_empty() {
            shift_right_once(&mut mutated_slice[..mutated_len]);
        }

        mutated_slice[0] = MaybeUninit::new(value);

        // SAFETY: mutated_slice is now fully initialized.
        unsafe {
            set_len.set_len(len + 1);
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

        let new_len =
            (small.marker >> 1) + u8::try_from(values.len()).expect("values.len() <= N <= 127");
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
    /// - `new_cap` must be greater than or equal to `self.len()`.
    unsafe fn move_small_to_large(&mut self, new_cap: usize) {
        // SAFETY: function safety invariant
        let small = unsafe { &mut self.0.small };
        let data = small.data.as_mut_ptr().cast::<T>();
        let small_len = small.marker >> 1;
        let data_slice = ptr::slice_from_raw_parts_mut(data, small_len.into());

        let large = unsafe { Large::new(new_cap, data_slice) };

        self.0.large = ManuallyDrop::new(large);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `WordVec<T, N>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity results in integer overflow.
    pub fn reserve(&mut self, additional: usize) {
        self.reserve_with(|args| {
            let req = args.len.checked_add(additional).expect("capacity overflow");
            if req <= args.cap {
                args.cap
            } else if req <= args.cap * 2 {
                args.cap * 2
            } else {
                req
            }
        });
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given `WordVec<T, N>`.
    /// Unlike [`reserve`](Self::reserve), this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`reserve`](Self::reserve) if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity results in integer overflow.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.reserve_with(|args| {
            let req = args.len.checked_add(additional).expect("capacity overflow");
            req.max(args.cap)
        });
    }

    fn reserve_with(&mut self, get_new_cap: impl FnOnce(ReserveArgs) -> usize) {
        match self.0.parse_marker() {
            ParsedMarker::Small(len) => {
                let len = usize::from(len);
                let new_cap = get_new_cap(ReserveArgs { len, cap: N });
                if new_cap > N {
                    // SAFETY: parsed marker as small,
                    // and new_cap > N >= len
                    unsafe {
                        self.move_small_to_large(new_cap);
                    }
                }
            }
            ParsedMarker::Large => {
                // SAFETY: parsed marker as large
                let large = unsafe { &mut self.0.large };
                let (&Allocated { len, cap, .. }, _) = large.as_allocated();
                let new_cap = get_new_cap(ReserveArgs { len, cap });
                if new_cap > cap {
                    large.grow_exact(new_cap);
                }
            }
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// If the new capacity fits into the inlined layout,
    /// the data is moved to the inlined layout.
    /// Otherwise, the allocation is reallocated to the smaller size.
    pub fn shrink_to_fit(&mut self) { self.shrink_to_with(|args| args.len.max(N)); }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// If the new capacity fits into the inlined layout,
    /// the data is moved to the inlined layout.
    /// Otherwise, the allocation is reallocated to the smaller size.
    pub fn shrink_to(&mut self, min_cap: usize) {
        // new capacity must be:
        // - at least self.len(), so that data do not get truncated
        // - at least min_cap, as requested
        // - at least N, because capacity can never be less than N
        self.shrink_to_with(|args| args.len.max(min_cap).max(N));
    }

    fn shrink_to_with(&mut self, get_new_cap: impl FnOnce(ShrinkToArgs) -> usize) {
        if let ParsedMarker::Small(_) = self.0.parse_marker() {
            return; // small cannot be further shrunk
        }

        // SAFETY: marker is Large
        let large = unsafe { &mut *self.0.large };
        let alloc_ptr = large.0;
        // SAFETY: alloc_ptr is still valid.
        let &Allocated { len, .. } = unsafe { alloc_ptr.as_ref() };
        let large_layout = large.current_layout();

        let new_cap = get_new_cap(ShrinkToArgs { len });
        if new_cap == N {
            // SAFETY: alloc_ptr is still valid.
            let data_start = unsafe { Allocated::data_start(alloc_ptr) };

            self.0.small = ManuallyDrop::new(Small {
                marker: u8::try_from(len << 1)
                    .expect("len <= new_cap == N <= 127, so len * 2 <= 254")
                    | 1,
                data:   [const { MaybeUninit::<T>::uninit() }; N],
            });
            // SAFETY:
            // - data_start is derived from alloc_ptr, which must not point back to itself
            // - self.0 is now initialized as Small.
            // - data_start is still valid until alloc_ptr is deallocated below.
            unsafe {
                ptr::copy_nonoverlapping(data_start, (*self.0.small).data.as_mut_ptr().cast(), len);
            }

            // This is the last statement of this branch,
            // and alloc_ptr is no longer referenced since
            // its only reference was overwritten by writing to self.0.small above.
            unsafe {
                dealloc(alloc_ptr.as_ptr().cast(), large_layout);
            }
        } else {
            // SAFETY: alloc_ptr is still valid at this point, and new_cap > N > 0.
            let new_layout = Large::<T>::new_layout(new_cap);
            let new_alloc_ptr =
                unsafe { realloc(alloc_ptr.as_ptr().cast(), large_layout, new_layout.size()) };
            match NonNull::new(new_alloc_ptr) {
                None => {
                    handle_alloc_error(new_layout);
                }
                Some(new_alloc_ptr) => {
                    large.0 = new_alloc_ptr.cast();
                    // SAFETY: large.0 has just been updated to a new valid allocation.
                    unsafe {
                        large.0.as_mut().cap = new_cap;
                    }
                }
            }
        }
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
        // SAFETY: index < `old_len`, so `mutated_slice` must not be empty.
        let removed = unsafe { mutated_slice.first_mut().unwrap_unchecked().assume_init_read() };
        shift_left_once(mutated_slice);
        Some(removed)
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

    /// Removes the last item.
    /// Returns `None` if the vector is empty.
    ///
    /// The vector capacity is unchanged.
    pub fn pop(&mut self) -> Option<T> {
        let last_index = self.len().checked_sub(1)?;
        self.try_swap_remove(last_index)
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

    /// Clears the vector, dropping all items.
    ///
    /// Does not change the capacity.
    pub fn clear(&mut self) { self.truncate(0); }

    /// Truncates the vector, dropping all items at and after index `len`.
    ///
    /// If `len` is greater or equal to the vector’s current length, this has no effect.
    ///
    /// Does not change the capacity.
    pub fn truncate(&mut self, len: usize) {
        let (capacity_slice, current_len, mut set_len) = self.as_uninit_slice_with_length_setter();
        if current_len <= len {
            return;
        }

        // SAFETY: len < current_len <= capacity
        unsafe { set_len.set_len(len) };

        // SAFETY: the truncated portion was previously initialized and now no longer reachable due
        // to setting the length to a smaller value.
        unsafe { slice_assume_init_drop(&mut capacity_slice[len..current_len]) };
    }

    /// Removes the subslice indicated by the given range from the vector,
    /// returning a double-ended iterator over the removed subslice.
    ///
    /// If the iterator is dropped before being fully consumed,
    /// it drops the remaining removed elements.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Leaking
    /// The vector is initially truncated to `range.start_bound()`.
    /// If the returned iterator is dropped before being fully consumed,
    /// the unconsumed elements as well as the elements behind the drained range are leaked.
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, T> {
        let (capacity_slice, current_len, mut set_len) = self.as_uninit_slice_with_length_setter();
        let initial_slice = &mut capacity_slice[..current_len];

        let start_drain = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n.checked_add(1).expect("start index overflow"),
            Bound::Unbounded => 0,
        };
        let end_drain = match range.end_bound() {
            Bound::Included(&n) => n.checked_add(1).expect("end index overflow"),
            Bound::Excluded(&n) => n,
            Bound::Unbounded => current_len,
        };

        assert!(start_drain <= end_drain, "start drain index must not exceed end drain index");
        assert!(end_drain <= current_len, "end drain index must not exceed current vector length");

        // SAFETY: start_drain <= end_drain <= current_len <= capacity
        // Reduces the length to the certainly initialized range.
        // Only increase it upon Drain::drop to reduce number of set_len calls,
        // which could be more expensive due to bitshift or heap access.
        unsafe { set_len.set_len(start_drain) };

        let mutated_slice = &mut initial_slice[start_drain..];
        let drained_offset = end_drain - start_drain;

        Drain {
            mutated_slice,
            total_drained: drained_offset,
            remain_start: 0,
            remain_end: drained_offset,
            set_len,
            set_len_base: start_drain,
        }
    }
}

/// A destructured component of `WordVec` to support setting length.
///
/// See [`WordVec::as_uninit_slice_with_length_setter()`].
pub struct LengthSetter<'a> {
    inner:    LengthSetterInner<'a>,
    #[cfg(debug_assertions)]
    capacity: usize,
}

enum LengthSetterInner<'a> {
    Small(&'a mut u8),
    Large(&'a mut usize),
}

impl LengthSetter<'_> {
    /// Sets the raw length of this vector.
    ///
    /// # Safety
    /// - `new_len` must be less than or equal to the current capacity.
    /// - The first `new_len` items of the vector must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        // The cfg check is required because self.capacity does not exist in release mode.
        #[cfg(debug_assertions)]
        debug_assert!(new_len <= self.capacity, "guaranteed by the caller of the writer function.");

        match self.inner {
            LengthSetterInner::Small(ref mut marker) => {
                // SAFETY: new_len <= N <= 127
                **marker = (unsafe { u8::try_from(new_len).unwrap_unchecked() } << 1) | 1;
            }
            LengthSetterInner::Large(ref mut len) => **len = new_len,
        }
    }

    /// Increments the raw length of this vector by 1.
    ///
    /// # Safety
    /// This has the same safety invariants as [`set_len`](Self::set_len),
    /// with `new_len` being the current raw length plus one.
    pub unsafe fn inc_len(&mut self) {
        match self.inner {
            LengthSetterInner::Small(ref mut marker) => {
                // SAFETY: the caller is required to ensure that this never overflows,
                // because current marker = length * 2 + 1 <= (N-1) * 2 + 1 = 2N - 1 <= 253.
                **marker = unsafe { marker.unchecked_add(2) };
            }
            LengthSetterInner::Large(ref mut len) => {
                // SAFETY: current length < capacity <= usize::MAX, so this will not overflow usize.
                **len = unsafe { len.unchecked_add(1) };
            }
        }
    }
}

/// Shifts `slice[1..]` to `slice[..slice.len()-1]`.
///
/// # Panics
/// Panics if `slice` is empty.
fn shift_left_once<T>(slice: &mut [MaybeUninit<T>]) {
    let moved_items = slice.len().checked_sub(1).expect("cannot shift empty slice");
    let ptr = slice.as_mut_ptr();
    unsafe {
        ptr::copy(ptr.add(1), ptr, moved_items);
    }
}

/// Shifts `slice[..slice.len()-1]` to `slice[1..]`.
///
/// # Panics
/// Panics if `slice` is empty.
fn shift_right_once<T>(slice: &mut [MaybeUninit<T>]) {
    let moved_items = slice.len().checked_sub(1).expect("cannot shift empty slice");
    let ptr = slice.as_mut_ptr();
    unsafe {
        ptr::copy(ptr, ptr.add(1), moved_items);
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
                    marker: u8::try_from(LENGTH << 1).expect("LENGTH * 2 <= N * 2 <= 254") | 1,
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

mod into_iter;
pub use into_iter::IntoIter;

// SAFETY: These are equivalent to the safety of `Vec<T>`.
unsafe impl<T: Send, const N: usize> Send for WordVec<T, N> {}
unsafe impl<T: Sync, const N: usize> Sync for WordVec<T, N> {}

mod trivial_traits;

mod drain;
pub use drain::Drain;

#[cfg(feature = "serde")]
mod serde_impl;
