use std::{
    fmt::{Debug, Display},
    ops::Deref,
};

use crate::vector::Vector;

/// A string type that is used on both the Rust and C++ side.
///
/// This type uses implicit data sharing to make it efficient to pass around
/// copied. When cloning, a reference to the data is cloned, not the data
/// itself. The data uses Copy-on-Write semantics, so the data is only cloned
/// when it is modified.
///
/// The string data is stored as UTF8-encoded bytes, and it is always terminated
/// with a null character.
#[derive(Clone, Default)]
#[repr(C)]
pub struct String {
    inner: Vector<u8>,
}

impl String {
    /// Returns a pointer to the underlying data.
    pub fn as_ptr(&self) -> *const u8 {
        self.inner.as_ptr()
    }

    /// Returns the size of the string, in bytes. This excludes the terminating
    /// null character.
    pub fn len(&self) -> usize {
        self.inner.len().saturating_sub(1)
    }

    /// Returns true if the String is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice to the string
    pub fn as_str(&self) -> &str {
        // Safety: self.as_ptr is a pointer from the inner which has utf-8
        unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(self.as_ptr(), self.len()))
        }
    }
}

impl Deref for String {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl From<&str> for String {
    fn from(value: &str) -> Self {
        String {
            inner: Vector::from_iter(value.as_bytes().iter().cloned().chain(core::iter::once(0))),
        }
    }
}

impl From<std::string::String> for String {
    fn from(s: std::string::String) -> Self {
        s.as_str().into()
    }
}

impl From<&std::string::String> for String {
    fn from(s: &std::string::String) -> Self {
        s.as_str().into()
    }
}

impl Debug for String {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl Display for String {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl AsRef<str> for String {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

/// for cbindgen.
#[allow(non_camel_case_types)]
type c_char = u8;

#[no_mangle]
/// Returns a nul-terminated pointer for this string.
/// The returned value is owned by the string, and should not be used after any
/// mutable function have been called on the string, and must not be freed.
pub extern "C" fn resolvo_string_bytes(ss: &String) -> *const c_char {
    if ss.is_empty() {
        "\0".as_ptr()
    } else {
        ss.as_ptr()
    }
}

#[no_mangle]
/// Destroy the shared string
pub unsafe extern "C" fn resolvo_string_drop(ss: *const String) {
    core::ptr::read(ss);
}

#[no_mangle]
/// Increment the reference count of the string.
/// The resulting structure must be passed to resolvo_string_drop
pub unsafe extern "C" fn resolvo_string_clone(out: *mut String, ss: &String) {
    core::ptr::write(out, ss.clone())
}

#[no_mangle]
/// Safety: bytes must be a valid utf-8 string of size len without null inside.
/// The resulting structure must be passed to resolvo_string_drop
pub unsafe extern "C" fn resolvo_string_from_bytes(
    out: *mut String,
    bytes: *const c_char,
    len: usize,
) {
    let str = core::str::from_utf8(core::slice::from_raw_parts(bytes, len)).unwrap();
    core::ptr::write(out, String::from(str));
}
