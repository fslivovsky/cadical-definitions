#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "definition_extractor.hpp"

namespace py = pybind11;

using namespace definability_interpolation;

PYBIND11_MODULE(definition_extractor_module, m) {
    py::class_<definition_extractor>(m, "definition_extractor")
        .def(py::init<>())  // Default constructor
        .def("add_clause", &definition_extractor::add_clause)
        .def("append_formula", &definition_extractor::append_formula)
        .def("has_definition", &definition_extractor::has_definition)
        .def("get_definition", &definition_extractor::get_definition);
}

