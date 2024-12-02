cmake_minimum_required(VERSION 3.10)

project(Cadical-Interpolate)

if(CMAKE_BUILD_TYPE MATCHES Debug)
    set(CONFIGURE_COMMAND configure --debug)
else()
    set(CONFIGURE_COMMAND configure)
endif()

include(ExternalProject)
ExternalProject_Add(cadical
    SOURCE_DIR ${CMAKE_SOURCE_DIR}/cadical
    CONFIGURE_COMMAND ${CMAKE_SOURCE_DIR}/cadical/${CONFIGURE_COMMAND}
    BUILD_COMMAND make
    INSTALL_COMMAND ""
    BUILD_IN_SOURCE 1
)

set(ABC_USE_NAMESPACE abc)
add_subdirectory(abc EXCLUDE_FROM_ALL)
# Remove any previous -fno-exceptions flag
message(STATUS "CXXFLAGS: ${ABC_CXXFLAGS}")
string(REPLACE "-fno-exceptions" "" ABC_CXXFLAGS "${ABC_CXXFLAGS}")
#target_compile_options(libabc-pic PRIVATE -fexceptions)

# ExternalProject_Add(abc
#     SOURCE_DIR ${CMAKE_SOURCE_DIR}/abc
#     CMAKE_ARGS -DABC_NAMESPACE=abc -DABC_USE_PIC=1
#     INSTALL_COMMAND ""
# )

# Set the C++ Standard to C++20.
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_subdirectory(src)
#add_subdirectory(python)
