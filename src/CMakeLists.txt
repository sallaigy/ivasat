set(SOURCES Solver.cpp DimacsParser.cpp main.cpp)

add_library(libivasat ${SOURCES})

add_executable(ivasat main.cpp)
target_link_libraries(ivasat libivasat)
