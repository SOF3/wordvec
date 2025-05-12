//! Polyfilled unstable APIs from the `maybe_uninit_slice` feature.

#![allow(clippy::pedantic)] // these are problems from libcore implementation.

use core::mem::MaybeUninit;
use core::ptr;

/// Gets a shared reference to the contained value.
/// Copied from [`slice::assume_init_ref()`].
///
/// # Safety
///
/// Calling this when the content is not yet fully initialized causes undefined
/// behavior: it is up to the caller to guarantee that every `MaybeUninit<T>` in
/// the slice really is in an initialized state.
pub const unsafe fn slice_assume_init_ref<T>(slice: &[MaybeUninit<T>]) -> &[T] {
    // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees that
    // `slice` is initialized, and `MaybeUninit` is guaranteed to have the same layout as `T`.
    // The pointer obtained is valid since it refers to memory owned by `slice` which is a
    // reference and thus guaranteed to be valid for reads.
    unsafe { &*(slice as *const [MaybeUninit<T>] as *const [T]) }
}

/// Gets a mutable (unique) reference to the contained value.
///
/// # Safety
///
/// Calling this when the content is not yet fully initialized causes undefined
/// behavior: it is up to the caller to guarantee that every `MaybeUninit<T>` in the
/// slice really is in an initialized state. For instance, `.assume_init_mut()` cannot
/// be used to initialize a `MaybeUninit` slice.
pub const unsafe fn slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: similar to safety notes for `slice_assume_init_ref`, but we have a
    // mutable reference which is also guaranteed to be valid for writes.
    unsafe { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

/// Drops the contained values in place.
///
/// # Safety
///
/// It is up to the caller to guarantee that every `MaybeUninit<T>` in the slice
/// really is in an initialized state. Calling this when the content is not yet
/// fully initialized causes undefined behavior.
///
/// On top of that, all additional invariants of the type `T` must be
/// satisfied, as the `Drop` implementation of `T` (or its members) may
/// rely on this. For example, setting a `Vec<T>` to an invalid but
/// non-null address makes it initialized (under the current implementation;
/// this does not constitute a stable guarantee), because the only
/// requirement the compiler knows about it is that the data pointer must be
/// non-null. Dropping such a `Vec<T>` however will cause undefined
/// behaviour.
pub unsafe fn slice_assume_init_drop<T>(slice: &mut [MaybeUninit<T>]) {
    if !slice.is_empty() {
        // SAFETY: the caller must guarantee that every element of `slice`
        // is initialized and satisfies all invariants of `T`.
        // Dropping the value in place is safe if that is the case.
        unsafe { ptr::drop_in_place(slice as *mut [MaybeUninit<T>] as *mut [T]) }
    }
}
