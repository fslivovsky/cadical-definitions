cmake_minimum_required(VERSION 3.10)

# Find Pybind11
set(PYBIND11_FINDPYTHON ON)
find_package(pybind11 CONFIG)

if(pybind11_FOUND)
    pybind11_add_module(definition_extractor_module definition_extractor_bindings.cpp)
    target_include_directories(definition_extractor_module PRIVATE ${CMAKE_SOURCE_DIR}/src/)
    target_link_libraries(definition_extractor_module PRIVATE definition_extractor)
else()
    message(WARNING "Pybind11 not found - Python bindings will not be built.")
endif()
