use alloc::alloc::{alloc, handle_alloc_error, realloc};
use core::alloc::Layout;
use core::hint::assert_unchecked;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};

pub(crate) union Inner<T, const N: usize> {
    pub(crate) small: ManuallyDrop<Small<T, N>>,
    pub(crate) large: ManuallyDrop<Large<T>>,
}

impl<T, const N: usize> Inner<T, N> {
    pub(crate) const fn assert_generics() {
        const {
            assert!(N <= 127, "N must be less than or equal to 127 to fit in the marker byte");
            assert!(align_of::<usize>() >= 2, "usize must be aligned to 2 bytes");
        }
    }

    pub(crate) fn parse_marker(&self) -> ParsedMarker {
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
pub(crate) struct Small<T, const N: usize> {
    pub(crate) marker: u8,
    pub(crate) data:   [MaybeUninit<T>; N],
}

impl<T, const N: usize> Small<T, N> {
    pub(crate) const fn new_uninit(len: usize) -> Self {
        Self::new(len, [const { MaybeUninit::uninit() }; N])
    }

    pub(crate) const fn new(len: usize, data: [MaybeUninit<T>; N]) -> Self {
        Inner::<T, N>::assert_generics();

        #[expect(
            clippy::cast_possible_truncation,
            reason = "LENGTH <= N <= 127 must be within bounds of u7"
        )]
        Self { marker: (len << 1) as u8 | 1, data }
    }
}

#[cfg(target_endian = "big")]
compile_error!("Big-endian targets are not supported yet");

pub(crate) enum ParsedMarker {
    Small(u8),
    Large,
}

pub(crate) struct Large<T>(pub(crate) NonNull<Allocated<T>>);

impl<T> Large<T> {
    pub(crate) fn new_layout(cap: usize) -> Layout {
        let additional_size = size_of::<T>().checked_mul(cap).expect("new capacity is too large");
        let size = size_of::<Allocated<T>>()
            .checked_add(additional_size)
            .expect("new capacity is too large");
        let align = align_of::<Allocated<T>>();
        // SAFETY: size of Allocated<T> must be a multiple of align of Allocated<T>,
        // which must be a multiple of align of T due to the `data` field.
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }

    pub(crate) fn as_allocated(&self) -> (&Allocated<T>, *const T) {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        unsafe { (self.0.as_ref(), Allocated::data_start(self.0)) }
    }

    pub(crate) fn as_allocated_mut(&mut self) -> (&mut Allocated<T>, *mut T) {
        // SAFETY: the pointer is always valid as an invariant of this struct.
        // The `data_start` pointer does not alias the `&mut Allocated`
        // since `Allocated` only contains an empty array.
        unsafe { (self.0.as_mut(), Allocated::data_start(self.0)) }
    }

    pub(crate) fn current_layout(&self) -> Layout {
        let cap = self.as_allocated().0.cap;
        Self::new_layout(cap)
    }

    /// This function never reads or writes `Allocated.len`.
    /// This allows the local cache of `len` in `extend_large_iter`
    /// to remain valid when reallocation occurs during growth.
    pub(crate) fn grow(&mut self, min_new_cap: usize) -> usize {
        let mut new_cap = min_new_cap;

        let old_cap = self.as_allocated().0.cap;
        if let Some(double) = old_cap.checked_mul(2) {
            new_cap = new_cap.max(double);
        }

        self.grow_exact(new_cap);
        new_cap
    }

    pub(crate) fn grow_exact(&mut self, new_cap: usize) {
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

    pub(crate) fn extend_iter(&mut self, values: impl Iterator<Item = T>) {
        let (&Allocated { len, mut cap, .. }, _) = self.as_allocated();

        let (hint_min, _) = values.size_hint();
        let hint_len = len.checked_add(hint_min).expect("new length out of bounds");

        if hint_len > cap {
            cap = self.grow(hint_len);
        }

        let mut new_len = len;
        let mut values = values.fuse();

        while new_len < cap {
            // This simple loop allows better optimizations subject to the implementation of
            // `values`.
            if let Some(item) = values.next() {
                new_len += 1; // new_len < cap <= usize::MAX, so this will not overflow
                unsafe {
                    let dest = Allocated::<T>::data_start(self.0).add(new_len - 1);
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
                cap = self.grow(new_len);
            }

            unsafe {
                let dest = Allocated::<T>::data_start(self.0).add(new_len - 1);
                dest.write(item);
            }
        }

        // SAFETY:
        // - self.0 might have been reallocated, but accessing it through `self` is still correct.
        // - only one item pushed at a time
        unsafe {
            let mut allocated_ptr = self.0;
            allocated_ptr.as_mut().len = new_len;
        }
    }

    /// Create a new `Large` with a new allocation,
    /// and move the data from `src` to the new allocation.
    ///
    /// # Safety
    /// - `src` has the same invariants as [`ptr::drop_in_place`].
    /// - The data behind `src` is invalid after this function returns.
    pub(crate) unsafe fn new(cap: usize, src: *mut [T]) -> Self {
        let this = Self::new_empty(cap);

        // SAFETY: The underlying `Allocated` is now initialized with the correct capacity.
        unsafe {
            Allocated::extend(this.0, src);
        }

        this
    }

    /// Create a new `Large` with a new allocation and zero length.
    pub(crate) fn new_empty(cap: usize) -> Self {
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
/// Due to provenance, `data_start` cannot be directly converted to a slice reference;
/// the slice must always be derived from the allocation pointer (`NonNull<Allocated<T>>`)
/// directly.
#[repr(C)]
pub(crate) struct Allocated<T> {
    pub(crate) len: usize,
    pub(crate) cap: usize,
    data_start:     [T; 0], // alignment of T, without the size of T.
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
    pub(crate) unsafe fn extend(mut this: NonNull<Self>, src: *mut [T]) {
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
    pub(crate) unsafe fn extend_data(this: NonNull<Self>, src: *mut [T], old_len: usize) {
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
    pub(crate) unsafe fn data_start(this: NonNull<Self>) -> *mut T {
        unsafe { (&raw mut (*this.as_ptr()).data_start).cast() }
    }
}
