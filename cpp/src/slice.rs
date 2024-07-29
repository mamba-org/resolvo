use std::{fmt::Debug, marker::PhantomData, ptr::NonNull};

#[repr(C)]
#[derive(PartialEq)]
pub struct Slice<'a, T> {
    /// Invariant, this is a valid slice of len `len`
    ptr: NonNull<T>,
    len: usize,
    phantom: PhantomData<&'a [T]>,
}

impl<'a, T: Debug> Debug for Slice<'a, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_slice().fmt(f)
    }
}

// Need to implement manually otherwise it is not implemented if T do not
// implement Copy / Clone
impl<'a, T> Copy for Slice<'a, T> {}

impl<'a, T> Clone for Slice<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> Slice<'a, T> {
    /// Return a slice
    pub fn as_slice(self) -> &'a [T] {
        // Safety: it ptr is supposed to be a valid slice of given length
        unsafe { core::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }

    /// Create from a native slice
    pub const fn from_slice(slice: &'a [T]) -> Self {
        Slice {
            // Safety: a slice is never null
            ptr: unsafe { NonNull::new_unchecked(slice.as_ptr() as *mut T) },
            len: slice.len(),
            phantom: PhantomData,
        }
    }
}

impl<'a, T> From<&'a [T]> for Slice<'a, T> {
    fn from(slice: &'a [T]) -> Self {
        Self::from_slice(slice)
    }
}

impl<'a, T> core::ops::Deref for Slice<'a, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<'a, T> Default for Slice<'a, T> {
    fn default() -> Self {
        Self::from_slice(&[])
    }
}

/// Safety: Slice is the same as a rust slice, and a slice of Sync T is Sync
unsafe impl<T: Sync> Sync for Slice<'_, T> {}
/// Safety: Slice is the same as a rust slice, and a slice of Send T is Sync
unsafe impl<T: Sync> Send for Slice<'_, T> {}
