cmake_minimum_required(VERSION 3.24)
project(iva_sat)

set(CMAKE_CXX_STANDARD 20)

# Dependencies
include(FetchContent)

# Boost
FetchContent_Declare(
  boost_dynamic_bitset
  GIT_REPOSITORY "https://github.com/boostorg/dynamic_bitset"
  GIT_TAG boost-1.82.0
)

FetchContent_MakeAvailable(boost_dynamic_bitset)
include_directories(${boost_dynamic_bitset_SOURCE_DIR}/include)

include_directories(include)

add_subdirectory(src)
add_subdirectory(unittests)
