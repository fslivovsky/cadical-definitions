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
add_subdirectory(cadical-interface)
add_subdirectory(src)
add_subdirectory(python)
