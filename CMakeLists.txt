cmake_minimum_required(VERSION 3.24)
project(iva_sat)

set(CMAKE_CXX_STANDARD 20)

# Dependencies
include(FetchContent)

include_directories(include)

add_subdirectory(src)

option(IVASAT_ENABLE_SANITIZER "Enable sanitizer flags for debug builds" OFF)

if(IVASAT_ENABLE_SANITIZER)
  if (((CMAKE_CXX_COMPILER_ID STREQUAL "Clang") OR (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")))
    message(STATUS "Adding sanitizer flags")
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-omit-frame-pointer -fsanitize=address -fsanitize=undefined")
  else()
    message(STATUS "Sanitizer flags are only available with clang/gcc")
  endif()
endif()


enable_testing()
add_subdirectory(unittests)
