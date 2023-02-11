cmake_minimum_required(VERSION 3.24)
project(iva_sat)

set(CMAKE_CXX_STANDARD 20)

include_directories(include)

add_subdirectory(src)
add_subdirectory(unittests)


