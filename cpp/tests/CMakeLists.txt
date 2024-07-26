FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG v2.13.8)

FetchContent_MakeAvailable(Catch2)

include(CTest)

macro(resolvo_test NAME)
  add_executable(test_${NAME} ${NAME}.cpp)
  target_link_libraries(test_${NAME} PRIVATE Resolvo Catch2::Catch2)
  target_compile_definitions(
    test_${NAME} PRIVATE SOURCE_DIR=\"${CMAKE_CURRENT_SOURCE_DIR}/\")
  # Use debug version of run-time library to enable MSVC iterator debugging
  set_property(TARGET test_${NAME} PROPERTY MSVC_RUNTIME_LIBRARY
                                            MultiThreadedDebugDLL)
  add_test(NAME test_${NAME} COMMAND test_${NAME})

  if(MSVC)
    target_compile_options(test_${NAME} PRIVATE /W3)
  else()
    target_compile_options(test_${NAME} PRIVATE -Wall -Wextra -Werror)
  endif()

  if(CMAKE_CXX_COMPILER_ID STREQUAL GNU)
    # that warning has false positives
    target_compile_options(test_${NAME} PRIVATE -Wno-maybe-uninitialized)
  endif()
endmacro(resolvo_test)

resolvo_test(vector)
resolvo_test(string)
resolvo_test(solve)
