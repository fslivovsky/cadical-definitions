#include "cadical_solver.hpp"

#include <unistd.h>
#include <cassert>

#include <iostream>
#include <string>

#include "interrupt.hpp"

namespace definability_interpolation {

Cadical::CadicalTerminator Cadical::terminator;

Cadical::Cadical(): tracer(nullptr) {
  solver.connect_terminator(&terminator);
}

Cadical::Cadical(CaDiCaL::Tracer* tracer) {
  solver.set("inprocessing", false);
  this->tracer = tracer;
  solver.connect_proof_tracer(tracer, true);
}

Cadical::~Cadical() {
  if (tracer) {
    solver.disconnect_proof_tracer(tracer);
  }
  solver.disconnect_terminator();
}

bool Cadical::CadicalTerminator::terminate() {
  return interrupt_handler::interrupted(nullptr);
}

void Cadical::append_formula(const std::vector<std::vector<int>>& formula) {
  for (const auto& clause: formula) {
    add_clause(clause);
  }
}

void Cadical::add_clause(const std::vector<int>& clause) {
  solver.clause(clause);
}

void Cadical::assume(const std::vector<int>& assumptions) {
  for (auto l: assumptions) {
    solver.assume(l);
  }
}

void Cadical::set_assumptions(const std::vector<int>& assumptions) {
  solver.reset_assumptions();
  assume(assumptions);
}

int Cadical::solve(const std::vector<int>& assumptions) {
  set_assumptions(assumptions);
  return solve();
}

int Cadical::solve() {
  int result = solver.solve();
  if (interrupt_handler::interrupted(nullptr)) {
    throw interrupted_exception();
  }
  return result;
}

int Cadical::solve_limited(int conflict_limit) {
  solver.limit("conflicts", conflict_limit);
  return solve();
}

std::vector<int> Cadical::get_failed(const std::vector<int>& assumptions) {
  std::vector<int> failed_literals;
  for (auto l: assumptions) {
    if (solver.failed(l)) {
      failed_literals.push_back(l);
    }
  }
  return failed_literals;
}

std::vector<int> Cadical::get_values(const std::vector<int>& variables) {
  std::vector<int> assignment;
  for (auto v: variables) {
    assignment.push_back(val(v));
  }
  return assignment;
}

std::vector<int> Cadical::get_model() {
  std::vector<int> assignment;
  for (int v = 1; v <= solver.vars(); v++) {
    assignment.push_back(val(v));
  }
  return assignment;
}

int Cadical::val(int variable) {
  auto l = solver.val(variable);
  auto v = abs(l);
  if (v == variable) {
    return l;
  } else {
    return variable;
  }
}

}