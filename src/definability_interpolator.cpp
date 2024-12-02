#include "definability_interpolator.hpp"

#include <iostream>
#include <algorithm>
#include <cassert>
#include <unordered_set>

#include "opt/dar/dar.h"

using namespace abc; // Needed for macro expansion.

namespace definability_interpolation {

definability_interpolator::definability_interpolator(): empty_id(0) {
  abc::Dar_LibStart();
}

definability_interpolator::~definability_interpolator() {
  abc::Dar_LibStop();
}

void definability_interpolator::add_original_clause(uint64_t id, bool redundant, const std::vector<int>& clause, bool restored) {
  // If the clause contains the literal 1, then it belongs to the first part of the formula.
  bool in_first_part = std::find(clause.begin(), clause.end(), 1) != clause.end();
  if (in_first_part) {
    for (auto l: clause) {
      first_part_variables_set.insert(std::abs(l));
    }
  }
  clause_id_to_clause[id] = clause;
  clause_id_to_proofnode[id] = std::make_shared<binary_proofnode>(!in_first_part);
}

void definability_interpolator::add_derived_clause(uint64_t id, bool redundant, const std::vector<int>& clause, const std::vector<uint64_t>& antecedents) {
  clause_id_to_clause[id] = clause;
  clause_id_to_antecedents[id] = antecedents;
  // Add an entry in the derivation node map.
  clause_id_to_derivation_node[id] = std::make_shared<clause_derivation_node>(id, *this);
  for (auto antecedent_id: antecedents) {
    if (clause_id_to_derivation_node.contains(antecedent_id)) {
      clause_id_to_derivation_node[id]->antecedents.push_back(clause_id_to_derivation_node.at(antecedent_id));
    }
  }
  //std::cout << "Adding clause " << id << std::endl;
  //std::cout << "Number of antecedents: " << antecedents.size() << std::endl;
}

void definability_interpolator::delete_clause (uint64_t id, bool redundant, const std::vector<int>& clause) {
  //std::cout << "Requesting deletion of clause " << id << std::endl;
  delete_ids.push_back(id);
}

void definability_interpolator::add_assumption_clause(uint64_t id, const std::vector<int>& clause, const std::vector<uint64_t>& antecedents) {
  add_derived_clause(id, true, clause, antecedents);
}

void definability_interpolator::conclude_unsat(CaDiCaL::ConclusionType type, const std::vector<uint64_t>& clause_ids) {
  #ifndef NDEBUG
  assert(type != CaDiCaL::ConclusionType::CONSTRAINT && !clause_ids.empty() && clause_ids.size() == 1);
  #endif
  empty_id = clause_ids[0];
}

std::pair<int, std::vector<std::vector<int>>> definability_interpolator::get_interpolant_clauses(const std::vector<int>& shared_variables, int auxiliary_variable_start, bool rewrite_aig) {
  auto output_variable = auxiliary_variable_start;
  create_core_proofnodes();
  auto rootnode = clause_id_to_proofnode.at(empty_id);
  aig_man = abc::Aig_ManStart(shared_variables.size());
  auto aig_input_variables = construct_aig(shared_variables);
  Aig_ManCleanup(aig_man);
  // Rewrite AIG if necessary.
  if (abc::Aig_ManNodeNum(aig_man) > 0 && rewrite_aig) {
    std::cout << "Number of nodes before: " << Aig_ManNodeNum(aig_man) << std::endl;
    aig_man = Dar_ManRewriteDefault(aig_man);
    std::cout << "Number of nodes after: " << Aig_ManNodeNum(aig_man) << std::endl;
  }
  std::vector<std::vector<int>> interpolant_clauses;
  interpolant_clauses.reserve(Aig_ManNodeNum(aig_man));
  abc::Vec_Ptr_t * vNodes;
  abc::Aig_Obj_t * pObj, * pConst1 = NULL;
  int i;
  assert(abc::Aig_ManCoNum(aig_man) == 1);
  // check if constant is used
  Aig_ManForEachCo( aig_man, pObj, i) {
    if (abc::Aig_ObjIsConst1(abc::Aig_ObjFanin0(pObj)))
      pConst1 = abc::Aig_ManConst1(aig_man);
  }
  // Assign shared variables to CIs.
  Aig_ManForEachCi( aig_man, pObj, i) {
    pObj->iData = aig_input_variables[i];
  }
  // collect nodes in the DFS order
  vNodes = abc::Aig_ManDfs(aig_man, 1);
  // assign IDs to objects
  Aig_ManForEachCo( aig_man, pObj, i ) {
    pObj->iData = auxiliary_variable_start++;
  }
  abc::Aig_ManConst1(aig_man)->iData = auxiliary_variable_start++;
  Vec_PtrForEachEntry( abc::Aig_Obj_t *, vNodes, pObj, i ) {
    pObj->iData = auxiliary_variable_start++;
  }
  // Add clauses from Tseitin conversion.
  if (pConst1) { // Constant 1 if necessary.
    interpolant_clauses.push_back( { pConst1->iData } );
  }
  Vec_PtrForEachEntry( abc::Aig_Obj_t *, vNodes, pObj, i ) {
    auto variable_output = pObj->iData;
    auto variable_input0 = abc::Aig_ObjFanin0(pObj)->iData;
    auto variable_input1 = abc::Aig_ObjFanin1(pObj)->iData;
    auto literal_input0 = Aig_ObjFaninC0(pObj) ? -variable_input0 : variable_input0;
    auto literal_input1 = Aig_ObjFaninC1(pObj) ? -variable_input1 : variable_input1;
    interpolant_clauses.push_back( { literal_input0, -variable_output } );
    interpolant_clauses.push_back( { literal_input1, -variable_output } );
    interpolant_clauses.push_back( { -literal_input0, -literal_input1, variable_output } );
  }
  // Write clauses for PO.
  Aig_ManForEachCo( aig_man, pObj, i ) {
    auto variable_output = pObj->iData;
    auto variable_input0 = abc::Aig_ObjFanin0(pObj)->iData;
    auto literal_input0 = Aig_ObjFaninC0(pObj) ? -variable_input0 : variable_input0;
    interpolant_clauses.push_back( { literal_input0, -variable_output } );
    interpolant_clauses.push_back( { -literal_input0, variable_output } );
  }
  abc::Vec_PtrFree(vNodes);
  abc::Aig_ManStop(aig_man);
  return std::make_pair(output_variable, interpolant_clauses);
}

// Get the clause ids in the core of the proof that do not already have a proofnode.
std::vector<uint64_t> definability_interpolator::get_core() const {
  #ifndef NDEBUG
  assert(empty_id != 0);
  #endif
  std::vector<uint64_t> core;
  std::vector<std::pair<uint64_t, int>> id_queue = {{empty_id, 0}};
  std::unordered_set<uint64_t> done;
  while (!id_queue.empty()) {
    auto [id, antecedent_index]  = id_queue.back();
    id_queue.pop_back();
    if (done.contains(id) || !clause_id_to_antecedents.contains(id) || clause_id_to_proofnode.contains(id)) {
      continue;
    }
    if (antecedent_index == clause_id_to_antecedents.at(id).size()) {
      // All antecedents have been processed.
      core.push_back(id);
      done.insert(id);
      continue;
    }
    // Go to the next antecedent.
    id_queue.push_back({id, antecedent_index + 1});
    id_queue.push_back({clause_id_to_antecedents.at(id)[antecedent_index], 0});
  }
  return core;
}

uint8_t definability_interpolator::mark_literal (int literal) {
  int index = std::abs (literal);
  uint8_t mask = (literal < 0) ? 2 : 1;
  uint8_t was_marked = marks[index];
  if (!was_marked)
    marking_history.push_back(index);
  if (!(was_marked & mask))
    marks[index] |= mask;
  return was_marked & ~mask;
}

void definability_interpolator::unmark_all() {
  for (auto& index: marking_history) {
    marks[index] = 0;
  }
  marking_history.clear();
}

void definability_interpolator::create_derived_proofnode(uint64_t id) {
  const auto& antecedents = clause_id_to_antecedents.at(id);
  // All antecedents must already have a proofnode.
  #ifndef NDEBUG
  for (auto &clause_id: antecedents)
    assert(clause_id_to_proofnode.contains(clause_id));
  #endif

  auto running_proofnode = clause_id_to_proofnode.at(antecedents.back());

  for (int i = antecedents.size() - 1; i >= 0; i--) {
    auto antecedent_id = antecedents[i];
    auto antecedent_clause = clause_id_to_clause.at(antecedent_id);
    auto antecedent_proofnode = clause_id_to_proofnode.at(antecedent_id);
    for (auto literal: antecedent_clause) {
      if (!mark_literal(literal))
        continue;
      running_proofnode = std::make_shared<binary_proofnode>(literal, antecedent_proofnode, running_proofnode);
    }
  }
  unmark_all();
  clause_id_to_proofnode[id] = running_proofnode;
  //std::cout << "Creating proofnode for clause " << id << std::endl;
  if (clause_id_to_derivation_node.contains(id)) {
    clause_id_to_derivation_node.at(id)->antecedents.clear(); // It's safe to delete the antecedents now.
  }
}

void definability_interpolator::create_core_proofnodes() {
  auto core = get_core();
  std::sort(core.begin(), core.end());
  // Create proofnodes for each clause in the core.
  for (auto it = core.begin(); it != core.end(); it++) {
    create_derived_proofnode(*it);
  }
}

void definability_interpolator::process_node(const std::shared_ptr<binary_proofnode>& proofnode, std::unordered_map<std::shared_ptr<binary_proofnode>, abc::Aig_Obj_t*>& proofnode_to_aig_node, std::unordered_map<int, abc::Aig_Obj_t*>& variable_to_ci, std::vector<int>& aig_input_variables, std::unordered_set<int>& shared_variables_set) {
  // The node must not have been processed.
  assert(!proofnode_to_aig_node.contains(proofnode));
  if (proofnode->left == nullptr && proofnode->right == nullptr) {
    // Leaf node: constant 0 or 1.
    proofnode_to_aig_node[proofnode] = proofnode->label ? abc::Aig_ManConst1(aig_man) : abc::Aig_ManConst1(aig_man);
  } else {
    // Both left and right nodes ought to be present.
    assert(proofnode->left && proofnode->right);
    auto left_node = proofnode_to_aig_node.at(proofnode->left);
    auto right_node = proofnode_to_aig_node.at(proofnode->right);
    assert(proofnode->label);
    int variable = abs(proofnode->label);
    if (shared_variables_set.contains(variable)) {
      // If there's no CI for the variable, create one.
      if (!variable_to_ci.contains(variable)) {
        aig_input_variables.push_back(variable);
        variable_to_ci[variable] = abc::Aig_ObjCreateCi(aig_man);
      }
      // Create an ITE node.
      auto variable_node = variable_to_ci.at(variable);
      proofnode_to_aig_node[proofnode] = abc::Aig_Mux(aig_man, abc::Aig_NotCond(variable_node, proofnode->label > 0), left_node, right_node);
    } else if (first_part_variables_set.contains(variable)) {
      // If the variable is local to the first part, create an OR node.
      proofnode_to_aig_node[proofnode] = abc::Aig_Or(aig_man, left_node, right_node);
    } else {
      // If the variable is local to the second part, create an AND node.
      proofnode_to_aig_node[proofnode] = abc::Aig_And(aig_man, left_node, right_node);
    }
  }
}

std::vector<int> definability_interpolator::construct_aig(const std::vector<int>& shared_variables) {
  std::unordered_map<std::shared_ptr<binary_proofnode>, abc::Aig_Obj_t*> proofnode_to_aig_node;
  std::unordered_map<int, abc::Aig_Obj_t*> variable_to_ci;
  std::vector<int> aig_input_variables;
  std::unordered_set<int> shared_variables_set(shared_variables.begin(), shared_variables.end());

  assert(clause_id_to_proofnode.contains(empty_id));
  auto rootnode = clause_id_to_proofnode.at(empty_id);
  assert(rootnode != nullptr);

  std::vector<std::shared_ptr<binary_proofnode>> stack;
  std::vector<std::shared_ptr<binary_proofnode>> processed_nodes;
  stack.push_back(rootnode);

  while (!stack.empty()) {
    auto node = stack.back();
    stack.pop_back();

    if (node->flag) {
      // If the node has already been processed, skip it.
      continue;
    }

    if ((node->left && !node->left->flag) || (node->right && !node->right->flag)) {
      // If any of the child nodes are not processed, push this node back into the stack.
      stack.push_back(node);
      // Push unprocessed child nodes into the stack.
      if (node->right && !node->right->flag) {
        stack.push_back(node->right);
      }
      if (node->left && !node->left->flag) {
        stack.push_back(node->left);
      }
    } else {
      // If both child nodes are processed (or don't exist), we can process this node.
      process_node(node, proofnode_to_aig_node, variable_to_ci, aig_input_variables, shared_variables_set);
      processed_nodes.push_back(node);
      node->flag = true;
    }
  }
  // Reset flags for processed nodes.
  for (auto node : processed_nodes) {
    node->flag = false;
  }
  // Create PO.
  abc::Aig_ObjCreateCo(aig_man, proofnode_to_aig_node.at(rootnode));
  return aig_input_variables;
}

void definability_interpolator::delete_clauses() {
  for (auto id: delete_ids) {
    clause_id_to_derivation_node.erase(id);
  }
  delete_ids.clear();
}

void definability_interpolator::delete_clause(uint64_t id) {
  //std::cout << "Deleting clause " << id << std::endl;
  clause_id_to_antecedents.erase(id);
  clause_id_to_clause.erase(id);
  clause_id_to_proofnode.erase(id);
}

} // namespace definability_interpolation