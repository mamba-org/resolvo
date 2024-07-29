#pragma once

namespace resolvo {
template <typename T>
struct Slice {
    /// Note: this doesn't initialize Slice properly, but we need to keep the struct as compatible
    /// with C
    constexpr Slice() = default;
    /// Rust uses a NonNull, so even empty slices shouldn't use nullptr
    constexpr Slice(const T *ptr, uintptr_t len)
        : ptr(ptr ? const_cast<T *>(ptr) : reinterpret_cast<T *>(sizeof(T))), len(len) {}

    /// Returns a const pointer to the first element of this slice.
    const T *cbegin() const { return reinterpret_cast<const T *>(ptr); }

    /// Returns a const pointer that points past the last element of this slice.
    const T *cend() const { return ptr + len; }

    /// Returns a const pointer to the first element of this slice.
    const T *begin() const { return cbegin(); }

    /// Returns a const pointer that points past the last element of this slice.
    const T *end() const { return cend(); }

    /// Returns a pointer to the first element of this vector.
    T *begin() { return reinterpret_cast<T *>(ptr); }

    /// Returns a pointer that points past the last element of this vector. The
    /// pointer cannot be dereferenced, it can only be used for comparison.
    T *end() { return ptr + len; }

    /// Returns the number of elements in this vector.
    std::size_t size() const { return len; }

    /// Returns true if there are no elements on this vector; false otherwise.
    bool empty() const { return len == 0; }

    /// This indexing operator returns a reference to the `index`th element of this vector.
    T &operator[](std::size_t index) { return begin()[index]; }

private:
    T *ptr;
    uintptr_t len;
};
}  // namespace resolvo
