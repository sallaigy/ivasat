set(SOURCES Solver.cpp Clause.cpp DimacsParser.cpp main.cpp SolverUtils.cpp)

add_library(libivasat ${SOURCES})

add_executable(ivasat main.cpp)
target_link_libraries(ivasat libivasat)
