#pragma once

#include <string_view>

#include "resolvo_string_internal.h"

namespace resolvo {

/// A string type that is used on both the Rust and C++ side.
///
/// This type uses implicit data sharing to make it efficient to pass around
/// copied. When cloning, a reference to the data is cloned, not the data
/// itself. The data uses Copy-on-Write semantics, so the data is only cloned
/// when it is modified.
///
/// The string data is stored as UTF8-encoded bytes, and it is always terminated
/// with a null character.
struct String {
    /// Creates an empty default constructed string.
    String() { cbindgen_private::resolvo_string_from_bytes(this, "", 0); }

    /// Creates a new String from a string view. The underlying string data is copied.
    String(std::string_view s) {
        cbindgen_private::resolvo_string_from_bytes(this, s.data(), s.size());
    }

    /// Creates a new String from the null-terminated string pointer `s`. The underlying
    /// string data is copied. It is assumed that the string is UTF-8 encoded.
    String(const char *s) : String(std::string_view(s)) {}

    /// Creates a new String from \a other.
    String(const String &other) { cbindgen_private::resolvo_string_clone(this, &other); }

    /// Destroys this String and frees the memory if this is the last instance
    /// referencing it.
    ~String() { cbindgen_private::resolvo_string_drop(this); }

    /// Provides a view to the string data. The returned view is only valid as long as at
    /// least this String exists.
    operator std::string_view() const { return cbindgen_private::resolvo_string_bytes(this); }
    /// Provides a raw pointer to the string data. The returned pointer is only valid as long as at
    /// least this String exists.
    auto data() const -> const char * { return cbindgen_private::resolvo_string_bytes(this); }

    /// Assigns \a other to this string and returns a reference to this string.
    String &operator=(const String &other) {
        cbindgen_private::resolvo_string_drop(this);
        cbindgen_private::resolvo_string_clone(this, &other);
        return *this;
    }

    /// Assigns the string view \a s to this string and returns a reference to this string.
    /// The underlying string data is copied.  It is assumed that the string is UTF-8 encoded.
    String &operator=(std::string_view s) {
        cbindgen_private::resolvo_string_drop(this);
        cbindgen_private::resolvo_string_from_bytes(this, s.data(), s.size());
        return *this;
    }

    /// Assigns null-terminated string pointer s to this string and returns a reference
    /// to this string. The underlying string data is copied. It is assumed that the string
    /// is UTF-8 encoded.
    String &operator=(const char *s) { return *this = std::string_view(s); }

    /// Move-assigns `other` to this String instance.
    String &operator=(String &&other) {
        std::swap(inner, other.inner);
        return *this;
    }

    /// Writes the string to the specified stream and returns a reference to the stream.
    friend std::ostream &operator<<(std::ostream &stream, const String &string) {
        return stream << std::string_view(string);
    }

    /// Returns true if a is equal to b; otherwise returns false.
    friend bool operator==(const String &a, const String &b) {
        return std::string_view(a) == std::string_view(b);
    }
    /// Returns true if a is not equal to b; otherwise returns false.
    friend bool operator!=(const String &a, const String &b) {
        return std::string_view(a) != std::string_view(b);
    }

private:
    void *inner;
};

}  // namespace resolvo

namespace std {
template <>
struct hash<resolvo::String> {
    std::uint64_t operator()(const resolvo::String &str) const {
        std::hash<string_view> hash_fn;
        return hash_fn(str);
    }
};
}  // namespace std
