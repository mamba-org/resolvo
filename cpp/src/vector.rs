use std::{fmt::Debug, mem::MaybeUninit, ops::Deref, ptr::NonNull, sync::atomic};

#[repr(C)]
struct VectorHeader {
    refcount: atomic::AtomicIsize,
    size: usize,
    capacity: usize,
}

#[repr(C)]
struct VectorInner<T> {
    header: VectorHeader,
    data: MaybeUninit<T>,
}

#[repr(C)]
pub struct Vector<T> {
    inner: NonNull<VectorInner<T>>,
}

// Safety: We use atomic reference counting, and if T is Send, we can send the
// vector to another thread
unsafe impl<T: Send> Send for Vector<T> {}

impl<T> Drop for Vector<T> {
    fn drop(&mut self) {
        unsafe {
            if self
                .inner
                .cast::<VectorHeader>()
                .as_ref()
                .refcount
                .load(atomic::Ordering::Relaxed)
                < 0
            {
                return;
            }

            if self
                .inner
                .as_ref()
                .header
                .refcount
                .fetch_sub(1, atomic::Ordering::SeqCst)
                == 1
            {
                drop_inner(self.inner)
            }
        }
    }
}

impl<T> Clone for Vector<T> {
    fn clone(&self) -> Self {
        unsafe {
            if self
                .inner
                .cast::<VectorHeader>()
                .as_ref()
                .refcount
                .load(atomic::Ordering::Relaxed)
                > 0
            {
                self.inner
                    .as_ref()
                    .header
                    .refcount
                    .fetch_add(1, atomic::Ordering::SeqCst);
            }
            Vector { inner: self.inner }
        }
    }
}

impl<T> Vector<T> {
    /// Create a new empty array with a pre-allocated capacity in number of
    /// items
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: alloc_with_capacity(capacity),
        }
    }

    /// Returns a pointer to the first element of the array.
    pub fn as_ptr(&self) -> *const T {
        unsafe { self.inner.as_ref().data.as_ptr() }
    }

    /// Returns the number of elements in the array
    pub fn len(&self) -> usize {
        unsafe { self.inner.cast::<VectorHeader>().as_ref().size }
    }

    /// Returns true if the Vector is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return a slice to the array
    pub fn as_slice(&self) -> &[T] {
        if self.is_empty() {
            &[]
        } else {
            // Safety: When len > 0, we know that the pointer holds an array of
            // the size of len
            unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
        }
    }

    /// Returns the number of elements the vector can hold without reallocating,
    /// when not shared
    fn capacity(&self) -> usize {
        unsafe { self.inner.cast::<VectorHeader>().as_ref().capacity }
    }
}

impl<T: Clone> Vector<T> {
    /// Ensure that the reference count is 1 so the array can be changed.
    /// If that's not the case, the array will be cloned
    fn detach(&mut self, new_capacity: usize) {
        let is_shared = unsafe {
            self.inner
                .as_ref()
                .header
                .refcount
                .load(atomic::Ordering::Relaxed)
        } != 1;
        if !is_shared && new_capacity <= self.capacity() {
            return;
        }
        let mut new_array = Vector::with_capacity(new_capacity);
        core::mem::swap(&mut self.inner, &mut new_array.inner);
        let mut size = 0;
        for x in new_array.into_iter() {
            assert_ne!(size, new_capacity);
            unsafe {
                core::ptr::write(self.inner.as_mut().data.as_mut_ptr().add(size), x);
                size += 1;
                self.inner.as_mut().header.size = size;
            }
            if size == new_capacity {
                break;
            }
        }
    }

    /// Adds an element to the array. If the array was shared, this will make a
    /// copy of the array.
    pub fn push(&mut self, value: T) {
        self.detach(determine_capacity_for_growth(
            self.capacity(),
            self.len() + 1,
            core::mem::size_of::<T>(),
        ));
        unsafe {
            core::ptr::write(
                self.inner
                    .as_mut()
                    .data
                    .as_mut_ptr()
                    .add(self.inner.as_mut().header.size),
                value,
            );
            self.inner.as_mut().header.size += 1;
        }
    }
}

impl<T> Deref for Vector<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> FromIterator<T> for Vector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let mut capacity = iter.size_hint().0;
        let mut result = Self::with_capacity(capacity);
        let mut size = 0;
        while let Some(x) = iter.next() {
            if size >= capacity {
                capacity = determine_capacity_for_growth(
                    capacity,
                    size + 1 + iter.size_hint().0,
                    core::mem::size_of::<T>(),
                );
                unsafe {
                    result
                        .inner
                        .as_ref()
                        .header
                        .refcount
                        .store(0, atomic::Ordering::Relaxed)
                };
                let mut iter = IntoIter(IntoIterInner::UnShared(result.inner, 0));
                result.inner = alloc_with_capacity::<T>(capacity);
                match &mut iter.0 {
                    IntoIterInner::UnShared(old_inner, begin) => {
                        while *begin < size {
                            unsafe {
                                core::ptr::write(
                                    result.inner.as_mut().data.as_mut_ptr().add(*begin),
                                    core::ptr::read(old_inner.as_ref().data.as_ptr().add(*begin)),
                                );
                                *begin += 1;
                                result.inner.as_mut().header.size = *begin;
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }
            debug_assert_eq!(result.len(), size);
            debug_assert!(result.capacity() > size);
            unsafe {
                core::ptr::write(result.inner.as_mut().data.as_mut_ptr().add(size), x);
                size += 1;
                result.inner.as_mut().header.size = size;
            }
        }
        result
    }
}

static SHARED_EMPTY_VEC: VectorHeader = VectorHeader {
    refcount: atomic::AtomicIsize::new(-1),
    size: 0,
    capacity: 0,
};

impl<T> Default for Vector<T> {
    fn default() -> Self {
        Vector {
            inner: NonNull::from(&SHARED_EMPTY_VEC).cast(),
        }
    }
}

impl<T: Debug> Debug for Vector<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T> AsRef<[T]> for Vector<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

/// Drops the inner vector and deallocates the memory. This is only really a
/// valid operation if the reference count is 0, otherwise there might be other
/// users.
unsafe fn drop_inner<T>(mut inner: NonNull<VectorInner<T>>) {
    debug_assert_eq!(
        inner
            .as_ref()
            .header
            .refcount
            .load(atomic::Ordering::Relaxed),
        0
    );
    let data_ptr = inner.as_mut().data.as_mut_ptr();
    for x in 0..inner.as_ref().header.size {
        core::ptr::drop_in_place(data_ptr.add(x));
    }
    std::alloc::dealloc(
        inner.as_ptr() as *mut u8,
        compute_inner_layout::<T>(inner.as_ref().header.capacity),
    )
}

impl<T: Clone> IntoIterator for Vector<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(unsafe {
            if self
                .inner
                .as_ref()
                .header
                .refcount
                .load(atomic::Ordering::Relaxed)
                == 1
            {
                let inner = self.inner;
                core::mem::forget(self);
                inner
                    .as_ref()
                    .header
                    .refcount
                    .store(0, atomic::Ordering::Relaxed);
                IntoIterInner::UnShared(inner, 0)
            } else {
                IntoIterInner::Shared(self, 0)
            }
        })
    }
}

enum IntoIterInner<T> {
    Shared(Vector<T>, usize),
    // Elements up to the usize member are already moved out
    UnShared(NonNull<VectorInner<T>>, usize),
}

impl<T> Drop for IntoIterInner<T> {
    fn drop(&mut self) {
        match self {
            IntoIterInner::Shared(..) => { /* drop of Vector takes care of it */ }
            IntoIterInner::UnShared(mut inner, begin) => unsafe {
                debug_assert_eq!(
                    inner
                        .as_ref()
                        .header
                        .refcount
                        .load(atomic::Ordering::Relaxed),
                    0
                );
                let data_ptr = inner.as_mut().data.as_mut_ptr();
                for x in (*begin)..inner.as_ref().header.size {
                    core::ptr::drop_in_place(data_ptr.add(x));
                }
                std::alloc::dealloc(
                    inner.as_ptr() as *mut u8,
                    compute_inner_layout::<T>(inner.as_ref().header.capacity),
                )
            },
        }
    }
}

/// An iterator that moves out of a Vector.
///
/// This `struct` is created by the `into_iter` method on [`Vector`]
/// (provided by the [`IntoIterator`] trait).
pub struct IntoIter<T>(IntoIterInner<T>);

impl<T: Clone> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IntoIterInner::Shared(array, moved) => {
                let result = array.as_slice().get(*moved).cloned();
                *moved += 1;
                result
            }
            IntoIterInner::UnShared(inner, begin) => unsafe {
                if *begin < inner.as_ref().header.size {
                    let r = core::ptr::read(inner.as_ref().data.as_ptr().add(*begin));
                    *begin += 1;
                    Some(r)
                } else {
                    None
                }
            },
        }
    }
}

/// Determine the memory layout to allocate when a specific capacity of T is
/// requested.
fn compute_inner_layout<T>(capacity: usize) -> core::alloc::Layout {
    core::alloc::Layout::new::<VectorHeader>()
        .extend(core::alloc::Layout::array::<T>(capacity).unwrap())
        .unwrap()
        .0
}

/// Allocate the memory for a Vector with the given capacity. Returns an
/// `inner` with size and refcount set to 1
fn alloc_with_capacity<T>(capacity: usize) -> NonNull<VectorInner<T>> {
    let ptr = unsafe { std::alloc::alloc(compute_inner_layout::<T>(capacity)) };
    assert!(!ptr.is_null(), "allocation of {:?} bytes failed", capacity);
    unsafe {
        core::ptr::write(
            ptr as *mut VectorHeader,
            VectorHeader {
                refcount: 1.into(),
                size: 0,
                capacity,
            },
        );
    }
    NonNull::new(ptr).unwrap().cast()
}

/// Returns a new capacity suitable to store `required_cap` elements.
/// Loosely based on alloc::raw_vec::RawVec::grow_amortized.
fn determine_capacity_for_growth(
    current_cap: usize,
    required_cap: usize,
    elem_size: usize,
) -> usize {
    if current_cap >= required_cap {
        return current_cap;
    }
    let cap = core::cmp::max(current_cap * 2, required_cap);
    let min_non_zero_cap = if elem_size == 1 {
        8
    } else if elem_size <= 1024 {
        4
    } else {
        1
    };
    core::cmp::max(min_non_zero_cap, cap)
}

pub(crate) mod ffi {
    use super::*;

    #[no_mangle]
    /// This function is used for the low-level C++ interface to allocate the
    /// backing vector of a Vector.
    pub unsafe extern "C" fn resolvo_vector_allocate(size: usize, align: usize) -> *mut u8 {
        std::alloc::alloc(std::alloc::Layout::from_size_align(size, align).unwrap())
    }

    #[no_mangle]
    /// This function is used for the low-level C++ interface to deallocate the
    /// backing vector of a Vector
    pub unsafe extern "C" fn resolvo_vector_free(ptr: *mut u8, size: usize, align: usize) {
        std::alloc::dealloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).unwrap(),
        )
    }

    #[no_mangle]
    /// This function is used for the low-level C++ interface to initialize the
    /// empty Vector.
    pub unsafe extern "C" fn resolvo_vector_empty() -> *const u8 {
        &SHARED_EMPTY_VEC as *const _ as *const u8
    }
}
