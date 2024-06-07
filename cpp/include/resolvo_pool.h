#pragma once

#include <deque>
#include <unordered_map>

namespace resolvo {
/**
 * A Pool is an append only datastructure that associates a unique id with
 * every element added.
 *
 * Id's are allocated in a monotonically increasing fashion, starting from 0.
 */
template <typename ID, typename T>
struct Pool {
    Pool() = default;
    ~Pool() = default;

    /**
     * Adds the value to the pool and returns its associated id. If the
     * value is already in the pool, returns the id associated with it.
     */
    ID alloc(T value) {
        if (auto element = value_to_id.find(value); element != value_to_id.end()) {
            return element->second;
        }
        auto id = ID{static_cast<uint32_t>(values.size())};
        values.push_back(value);
        value_to_id.emplace(std::move(value), id);
        return id;
    }

    /**
     * Returns the value associated with the given id.
     */
    const T& operator[](ID id) const { return values[static_cast<size_t>(id.id)]; }

private:
    std::deque<T> values;
    std::unordered_map<T, ID> value_to_id;
};
}  // namespace resolvo
