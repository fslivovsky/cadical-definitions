cmake_minimum_required(VERSION 3.10)

project(Cadical-Definitions)

find_package(Threads REQUIRED)

include(ExternalProject)

ExternalProject_Add(abc
    SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/abc
    CMAKE_ARGS -DABC_USE_NAMESPACE=abc
    BUILD_COMMAND make libabc-pic
    INSTALL_COMMAND ""
)

# Set the C++ Standard to C++20.
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

option(DEFINITIONS_LIBRARY_ONLY "Build only the library." OFF)
option(DEFINITIONS_PYTHON_BINDINGS "Build Python bindings (requires pybind11)." OFF)

add_subdirectory(CLI11)
add_subdirectory(cadical-interface)
add_subdirectory(src)
if (DEFINITIONS_PYTHON_BINDINGS)
    add_subdirectory(python)
endif()
