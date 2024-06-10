cmake_minimum_required(VERSION 3.21)

# Select C++ and C as languages, as Corrosion needs ${CMAKE_C_COMPILER}
# for linking
project(Resolvo LANGUAGES C CXX VERSION 0.1.0)

# Add the Corrosion dependency (used to build Rust code)
include(FetchContent)
FetchContent_Declare(
    Corrosion
    GIT_REPOSITORY https://github.com/corrosion-rs/corrosion.git
    GIT_TAG v0.4.9
)
FetchContent_MakeAvailable(Corrosion)

# Add the Corrosion CMake module path to the list of paths to search for modules
list(PREPEND CMAKE_MODULE_PATH ${Corrosion_SOURCE_DIR}/cmake)
find_package(Rust 1.75 REQUIRED MODULE)

option(BUILD_SHARED_LIBS "Build Resolvo as shared library" ON)

set(RESOLVO_LIBRARY_CARGO_FLAGS "" CACHE STRING
    "Flags to pass to cargo when building the Resolvo runtime library")

if(BUILD_SHARED_LIBS)
    set(rustc_lib_type "cdylib")
    set(resolvo_cpp_impl "resolvo_cpp-shared")
    set(cmake_lib_type "SHARED")
else()
    set(rustc_lib_type "staticlib")
    set(resolvo_cpp_impl "resolvo_cpp-static")
    set(cmake_lib_type "STATIC")
endif()

corrosion_import_crate(MANIFEST_PATH "${CMAKE_CURRENT_SOURCE_DIR}/Cargo.toml"
    CRATES resolvo_cpp CRATE_TYPES bin ${rustc_lib_type})

add_library(Resolvo INTERFACE)
add_library(Resolvo::Resolvo ALIAS Resolvo)
target_link_libraries(Resolvo INTERFACE resolvo_cpp)

set_property(
    TARGET resolvo_cpp
    APPEND
    PROPERTY CORROSION_ENVIRONMENT_VARIABLES
    "RESOLVO_GENERATED_INCLUDE_DIR=${CMAKE_CURRENT_BINARY_DIR}/generated_include/"
)

file(GLOB api_headers RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}/include/"
        "${CMAKE_CURRENT_SOURCE_DIR}/include/*.h")

foreach(header IN LISTS api_headers)
    set_property(TARGET Resolvo APPEND PROPERTY PUBLIC_HEADER include/${header})
endforeach()

set(generated_headers
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_vector_internal.h
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_string_internal.h
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_internal.h
)

foreach(header IN LISTS generated_headers)
    set_property(TARGET Resolvo APPEND PROPERTY PUBLIC_HEADER ${header})
endforeach()

target_include_directories(Resolvo INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/generated_include>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include/resolvo>
)

export(TARGETS Resolvo resolvo_cpp
        NAMESPACE Resolvo:: FILE "${CMAKE_BINARY_DIR}/lib/cmake/Resolvo/ResolvoTargets.cmake")
install(EXPORT ResolvoTargets NAMESPACE Resolvo:: DESTINATION lib/cmake/Resolvo)
install(TARGETS Resolvo resolvo_cpp
    EXPORT ResolvoTargets LIBRARY DESTINATION lib PUBLIC_HEADER DESTINATION include/resolvo)

install(FILES $<TARGET_FILE:${resolvo_cpp_impl}> TYPE LIB)

if(WIN32)
    install(FILES $<TARGET_LINKER_FILE:${resolvo_cpp_impl}> TYPE LIB)
endif()

if(RESOLVO_BUILD_TESTING)
    add_subdirectory(tests)
endif()
