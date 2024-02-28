cmake_minimum_required(VERSION 3.24)
project(iva_sat)

set(CMAKE_CXX_STANDARD 20)

# Dependencies
include(FetchContent)

include_directories(include)

add_subdirectory(src)

enable_testing()
add_subdirectory(unittests)
