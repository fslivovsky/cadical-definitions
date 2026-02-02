cmake_minimum_required(VERSION 3.10)

add_library(interrupt interrupt.cpp interrupt.hpp)

add_library(abc-pic STATIC IMPORTED)
set_target_properties(abc-pic PROPERTIES
    IMPORTED_LOCATION ${CMAKE_BINARY_DIR}/abc-prefix/src/abc-build/libabc-pic.a
    INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_SOURCE_DIR}/abc/src/
)

find_library(READLINE_LIBRARY readline REQUIRED)

add_library(definability_interpolator definability_interpolator.cpp definability_interpolator.hpp)
target_compile_definitions(definability_interpolator PUBLIC "ABC_NAMESPACE=abc" "LIN64" "SIZEOF_VOID_P=8" "SIZEOF_LONG=8" "SIZEOF_INT=4" "ABC_USE_CUDD=1" "ABC_USE_READLINE" "DABC_USE_PTHREADS")
target_include_directories(definability_interpolator PUBLIC ${CMAKE_SOURCE_DIR}/cadical/src/)
add_dependencies(definability_interpolator abc)
#target_link_libraries(definability_interpolator PUBLIC libabc-pic)
target_include_directories(definability_interpolator PUBLIC ${CMAKE_SOURCE_DIR}/abc/src/)
target_link_libraries(definability_interpolator PUBLIC abc-pic ${READLINE_LIBRARY} dl)

add_library(cadical_solver cadical_solver.cpp cadical_solver.hpp)
target_include_directories(cadical_solver PUBLIC ${CMAKE_SOURCE_DIR}/cadical/src/)
add_dependencies(cadical_solver cadical)
target_link_libraries(cadical_solver PUBLIC ${CMAKE_SOURCE_DIR}/cadical/build/libcadical.a interrupt)

add_library(definition_extractor definition_extractor.cpp definition_extractor.hpp)
target_link_libraries(definition_extractor PUBLIC definability_interpolator cadical_solver)

add_executable(get_definitions main.cpp qdimacs.hpp)
target_link_libraries(get_definitions definition_extractor Threads::Threads CLI11::CLI11)
target_include_directories(get_definitions PRIVATE ${CMAKE_SOURCE_DIR}/abc/src/)

set_target_properties(get_definitions PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
)