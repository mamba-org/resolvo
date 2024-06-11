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

include(CMakePackageConfigHelpers)

function(_resolvo_write_configure_file)
    foreach(prop
        IMPORTED_LOCATION IMPORTED_LOCATION_DEBUG IMPORTED_LOCATION_RELEASE
        IMPORTED_LOCATION_RELWITHDEBINFO IMPORTED_LOCATION_MINSIZEREL
        IMPORTED_IMPLIB IMPORTED_IMPLIB_DEBUG IMPORTED_IMPLIB_RELEASE
        IMPORTED_IMPLIB_RELWITHDEBINFO IMPORTED_IMPLIB_MINSIZEREL)
        get_target_property(value ${resolvo_cpp_impl} ${prop})

        if(value)
            get_filename_component(value ${value} NAME)
            list(APPEND RESOLVO_LIB_PROPERTIES ${prop} "\${_IMPORT_PREFIX}/${CMAKE_INSTALL_LIBDIR}/${value}")
        endif()
    endforeach()

    foreach(prop IMPORTED_NO_SONAME IMPORTED_SONAME)
        get_target_property(value ${resolvo_cpp_impl} ${prop})
        if(value)
            list(APPEND RESOLVO_LIB_PROPERTIES ${prop} ${value})
        endif()
    endforeach()

    configure_package_config_file("cmake/ResolvoConfig.cmake.in" "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfig.cmake" INSTALL_DESTINATION lib/cmake/resolvo)
endfunction()

cmake_language(DEFER CALL _resolvo_write_configure_file)

write_basic_package_version_file(
    ${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfigVersion.cmake
    VERSION 0.1.0
    COMPATIBILITY SameMinorVersion
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfigVersion.cmake"
    DESTINATION lib/cmake/Resolvo
)

if(RESOLVO_BUILD_TESTING)
    add_subdirectory(tests)
endif()
