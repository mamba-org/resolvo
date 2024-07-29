#pragma once

#include <algorithm>
#include <atomic>
#include <initializer_list>
#include <memory>

#include "resolvo_slice.h"
#include "resolvo_vector_internal.h"

namespace resolvo {

/// A simple vector implementation that uses reference counting to share data
/// between multiple instances. The vector is implemented as a contiguous array
/// of elements. The vector is copy-on-write, meaning that when a vector is
/// copied, the data is not copied.
template <typename T>
struct Vector {
    /// Constucts a new empty vector.
    Vector()
        : inner(const_cast<Header *>(
              reinterpret_cast<const Header *>(cbindgen_private::resolvo_vector_empty()))) {}

    /// Creates a new vector that holds all the elements of the given std::initializer_list.
    Vector(std::initializer_list<T> args) : Vector(Vector::with_capacity(args.size())) {
        auto new_data = reinterpret_cast<T *>(inner + 1);
        auto input_it = args.begin();
        for (std::size_t i = 0; i < args.size(); ++i, ++input_it) {
            new (new_data + i) T(*input_it);
            inner->size++;
        }
    }

    /// Creates a vector of a given size, with default-constructed data.
    explicit Vector(size_t size) : Vector(Vector::with_capacity(size)) {
        auto new_data = reinterpret_cast<T *>(inner + 1);
        for (std::size_t i = 0; i < size; ++i) {
            new (new_data + i) T();
            inner->size++;
        }
    }

    /// Creates a vector of a given size, initialized with copies of `value`.
    explicit Vector(size_t size, const T &value) : Vector(Vector::with_capacity(size)) {
        auto new_data = reinterpret_cast<T *>(inner + 1);
        for (std::size_t i = 0; i < size; ++i) {
            new (new_data + i) T(value);
            inner->size++;
        }
    }

    /// Constructs the container with the contents of the range `[first, last)`.
    template <class InputIt>
    Vector(InputIt first, InputIt last)
        : Vector(Vector::with_capacity(std::distance(first, last))) {
        std::uninitialized_copy(first, last, begin());
        inner->size = inner->capacity;
    }

    /// Creates a new vector by copying the contents of another vector.
    /// Internally this function simplify increments the reference count of the
    /// other vector. Therefore no actual data is copied.
    Vector(const Vector &other) : inner(other.inner) {
        if (inner->refcount > 0) {
            ++inner->refcount;
        }
    }

    /// Destroys this vector. The underlying data is destroyed if no other
    /// vector references it.
    ~Vector() { drop(); }

    /// Provides a slice to the internal data. The returned Slice is only valid as long as at
    /// least this Vector exists.
    operator Slice<const T>() const { return Slice(begin(), size()); }

    /// Provides a slice to the internal data. The returned Slice is only valid as long as at
    /// least this Vector exists.
    operator Slice<T>() { return Slice(begin(), size()); }

    /// Assigns the data of \a other to this vector and returns a reference to this vector.
    Vector &operator=(const Vector &other) {
        if (other.inner == inner) {
            return *this;
        }
        drop();
        inner = other.inner;
        if (inner->refcount > 0) {
            ++inner->refcount;
        }
        return *this;
    }
    /// Move-assign's `other` to this vector and returns a reference to this vector.
    Vector &operator=(Vector &&other) {
        std::swap(inner, other.inner);
        return *this;
    }

    /// Returns a const pointer to the first element of this vector.
    const T *cbegin() const { return reinterpret_cast<const T *>(inner + 1); }

    /// Returns a const pointer that points past the last element of this vector. The
    /// pointer cannot be dereferenced, it can only be used for comparison.
    const T *cend() const { return cbegin() + inner->size; }

    /// Returns a const pointer to the first element of this vector.
    const T *begin() const { return cbegin(); }
    /// Returns a const pointer that points past the last element of this vector. The
    /// pointer cannot be dereferenced, it can only be used for comparison.
    const T *end() const { return cend(); }

    /// Returns a pointer to the first element of this vector.
    T *begin() {
        detach(inner->size);
        return reinterpret_cast<T *>(inner + 1);
    }

    /// Returns a pointer that points past the last element of this vector. The
    /// pointer cannot be dereferenced, it can only be used for comparison.
    T *end() {
        detach(inner->size);
        return begin() + inner->size;
    }

    /// Returns the number of elements in this vector.
    std::size_t size() const { return inner->size; }

    /// Returns true if there are no elements on this vector; false otherwise.
    bool empty() const { return inner->size == 0; }

    /// This indexing operator returns a reference to the `index`th element of this vector.
    T &operator[](std::size_t index) { return begin()[index]; }

    /// This indexing operator returns a const reference to the `index`th element of this vector.
    const T &operator[](std::size_t index) const { return begin()[index]; }

    /// Returns a reference to the `index`th element of this vector.
    const T &at(std::size_t index) const { return begin()[index]; }

    /// Appends the `value` as a new element to the end of this vector.
    void push_back(const T &value) {
        detach(inner->size + 1);
        new (end()) T(value);
        inner->size++;
    }

    /// Moves the `value` as a new element to the end of this vector.
    void push_back(T &&value) {
        detach(inner->size + 1);
        new (end()) T(std::move(value));
        inner->size++;
    }

    /// Clears the vector and removes all elements. The capacity remains unaffected.
    void clear() {
        if (inner->refcount != 1) {
            *this = Vector();
        } else {
            auto b = cbegin(), e = cend();
            inner->size = 0;
            for (auto it = b; it < e; ++it) {
                it->~T();
            }
        }
    }

    /// Returns true if the vector `a` has the same number of elements as `b`
    /// and all the elements also compare equal; false otherwise.
    friend bool operator==(const Vector &a, const Vector &b) {
        if (a.size() != b.size()) return false;
        return std::equal(a.cbegin(), a.cend(), b.cbegin());
    }

    /// Returns the current allocated capacity of this vector.
    std::size_t capacity() const { return inner->capacity; }

private:
    void detach(std::size_t expected_capacity) {
        if (inner->refcount == 1 && expected_capacity <= inner->capacity) {
            return;
        }
        auto new_array = Vector::with_capacity(expected_capacity);
        auto old_data = reinterpret_cast<const T *>(inner + 1);
        auto new_data = reinterpret_cast<T *>(new_array.inner + 1);
        for (std::size_t i = 0; i < inner->size; ++i) {
            new (new_data + i) T(old_data[i]);
            new_array.inner->size++;
        }
        *this = std::move(new_array);
    }

    void drop() {
        if (inner->refcount > 0 && (--inner->refcount) == 0) {
            auto b = cbegin(), e = cend();
            for (auto it = b; it < e; ++it) {
                it->~T();
            }
            cbindgen_private::resolvo_vector_free(reinterpret_cast<uint8_t *>(inner),
                                                  sizeof(Header) + inner->capacity * sizeof(T),
                                                  alignof(Header));
        }
    }

    static Vector with_capacity(std::size_t capacity) {
        auto mem = cbindgen_private::resolvo_vector_allocate(sizeof(Header) + capacity * sizeof(T),
                                                             alignof(Header));
        return Vector(new (mem) Header{{1}, 0, capacity});
    }

    struct Header {
        std::atomic<std::intptr_t> refcount;
        std::size_t size;
        std::size_t capacity;
    };
    static_assert(alignof(T) <= alignof(Header),
                  "Not yet supported because we would need to add padding");
    Header *inner;
    explicit Vector(Header *inner) : inner(inner) {}
};

}  // namespace resolvo
