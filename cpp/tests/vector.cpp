#define CATCH_CONFIG_MAIN
#include <resolvo_vector.h>

#include "catch2/catch.hpp"

SCENARIO("Vector") {
    resolvo::Vector<int> a{1, 2, 3, 4};
    REQUIRE(a.capacity() >= 4);
    REQUIRE(a.size() == 4);

    resolvo::Vector<int> b = a;
    REQUIRE(b.capacity() >= 4);
    REQUIRE(b.size() == 4);

    REQUIRE(a == b);

    b.push_back(4);
    REQUIRE(b.size() == 5);
    REQUIRE(a.size() == 4);
}
