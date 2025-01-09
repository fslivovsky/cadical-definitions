cmake_minimum_required(VERSION 3.10)

project(Cadical-Interpolate)

if(CMAKE_BUILD_TYPE MATCHES Debug)
    set(CONFIGURE_COMMAND configure --debug)
else()
    set(CONFIGURE_COMMAND configure)
endif()

find_package(Threads REQUIRED)

include(ExternalProject)
ExternalProject_Add(cadical
    SOURCE_DIR ${CMAKE_SOURCE_DIR}/cadical
    CONFIGURE_COMMAND CXXFLAGS=-fPIC ${CMAKE_SOURCE_DIR}/cadical/${CONFIGURE_COMMAND}
    BUILD_COMMAND make
    INSTALL_COMMAND ""
    BUILD_IN_SOURCE 1
)

ExternalProject_Add(abc
    SOURCE_DIR ${CMAKE_SOURCE_DIR}/abc
    CMAKE_ARGS -DABC_USE_NAMESPACE=abc
    BUILD_COMMAND make libabc-pic
    INSTALL_COMMAND ""
)

# Set the C++ Standard to C++20.
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_subdirectory(src)
add_subdirectory(python)
