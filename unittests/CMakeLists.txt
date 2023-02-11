enable_testing()

include(FetchContent)

# Load GoogleTest
FetchContent_Declare(
  gtest
  GIT_REPOSITORY "https://github.com/google/googletest"
  GIT_TAG release-1.11.0
)

set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(gtest)
include(GoogleTest)

set(TEST_SOURCES
  DimacsParserTest.cpp DimacsParserTest.cpp SolverTest.cpp)
add_executable(ivasat_test ${TEST_SOURCES})
target_link_libraries(ivasat_test gmock_main libivasat)

gtest_discover_tests(ivasat_test)
