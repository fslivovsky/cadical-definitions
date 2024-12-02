#include "definition_extractor.hpp"

#include <cassert>

namespace definability_interpolation {

definition_extractor::definition_extractor() : state(State::UNDEFINED), interpolator(), solver(&interpolator) {}

void definition_extractor::add_variable(int variable) {
  assert(variable > 0);
  while (variable >= equality_selector.size()) {
    equality_selector.push_back(0);
  }
  auto equal_selector = 3 * variable + 2;
  equality_selector[variable] = equal_selector;
  auto first_part_variable = translate_literal(variable, true);
  auto second_part_variable = translate_literal(variable, false);
  solver.append_formula({{-equal_selector, first_part_variable, -second_part_variable}, {-equal_selector, -first_part_variable, second_part_variable}});
}

int definition_extractor::translate_literal(int literal, bool first_part) {
  auto v = abs(literal);
  auto v_translated = 3 * v + first_part;
  return literal < 0 ? -v_translated : v_translated;
}

int definition_extractor::original_literal(int translated_literal) {
  auto v = abs(translated_literal);
  auto v_original = v / 3;
  if (v_original >= equality_selector.size()) {
    // This is an auxiliary variable introduced during interpolation.
    return translated_literal;
  }
  return translated_literal < 0 ? -v_original : v_original;
}

std::vector<int> definition_extractor::translate_clause(const std::vector<int>& clause, bool first_part) {
  std::vector<int> translated_clause;
  for (auto l: clause) {
    translated_clause.push_back(translate_literal(l, first_part));
  }
  return translated_clause;
}

void definition_extractor::original_clause(std::vector<int>& translated_clause) {
  for (auto& l: translated_clause) {
    l = original_literal(l);
  }
}

void definition_extractor::add_clause(const std::vector<int>& clause) {
  state = State::UNDEFINED;
  for (auto l: clause) {
    auto v = abs(l);
    if (v >= equality_selector.size() or equality_selector[v] == 0) {
      add_variable(v);
    }
  }
  auto first_part_clause = translate_clause(clause, true);
  first_part_clause.push_back(1);
  solver.add_clause(first_part_clause);
  solver.add_clause(translate_clause(clause, false));
}

void definition_extractor::append_formula(const std::vector<std::vector<int>>& formula) {
  for (const auto& clause: formula) {
    add_clause(clause);
  }
}

bool definition_extractor::has_definition(int variable, const std::vector<int>& shared_variables, const std::vector<int>& assumptions) {
  assert(variable > 0);
  state = State::UNDEFINED;
  std::vector<int> assumptions_internal;
  for (auto v: shared_variables) {
    if (v >= equality_selector.size() or equality_selector[v] == 0) {
      add_variable(v);
    }
    assumptions_internal.push_back(equality_selector[v]);
  }
  auto variable_first_part_true = translate_literal(variable, true);
  auto variable_second_part_false = -translate_literal(variable, false);
  // Translate external assumptions.
  auto assumptions_first_part = translate_clause(assumptions, true);
  assumptions_internal.insert(assumptions_internal.end(), assumptions_first_part.begin(), assumptions_first_part.end());
  std::vector<int> assumptions_second_part = translate_clause(assumptions, false);
  assumptions_internal.insert(assumptions_internal.end(), assumptions_second_part.begin(), assumptions_second_part.end());
  assumptions_internal.push_back(variable_first_part_true);
  assumptions_internal.push_back(variable_second_part_false);
  assumptions_internal.push_back(-1);
  bool has_definition = (solver.solve(assumptions_internal) == 20);
  if (has_definition) {
    state = State::DEFINED;
    last_shared_variables = shared_variables;
    last_variable = variable;
  }
  interpolator.delete_clauses();
  return has_definition;
}

std::pair<std::vector<std::vector<int>>, int> definition_extractor::get_definition(bool rewrite) {
  if (state != State::DEFINED) {
    throw UndefinedException();
  }
  state = State::UNDEFINED; // Can we make sure that repeated calls of get_definition are safe?
  auto [output_variable, definition] = interpolator.get_interpolant_clauses(translate_clause(last_shared_variables, true), 3 * equality_selector.size(), rewrite);
  interpolator.delete_clauses();
  for (auto& clause: definition) {
    original_clause(clause);
  }
  definition.push_back({ output_variable, -last_variable});
  definition.push_back({-output_variable,  last_variable});
  return std::make_pair(definition, 3 * equality_selector.size());
}

} // namespace definability_interpolation

