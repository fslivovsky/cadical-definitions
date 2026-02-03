#ifndef DEFINABILITY_INTERPOLATOR_HPP
#define DEFINABILITY_INTERPOLATOR_HPP

#include "tracer.hpp"

#include <unordered_set>
#include <unordered_map>
#include <memory>
#include <vector>
#include <tuple>

#include <iostream>

#include "aig/aig/aig.h"

namespace definability_interpolation {

class definability_interpolator : public CaDiCaL::Tracer
{
 public:
  definability_interpolator();
  ~definability_interpolator() override;

  // When an original clause is added, we have to determine (and remember) whether if it belongs to the first or second part
  // used in interpolation.
  void add_original_clause(int64_t id, bool redundant, const std::vector<int>& clause, bool restored = false) override;

  // Upon deriving a clause, we will store a reference to the clause and its antecedents.
  void add_derived_clause(int64_t id, bool redundant, int witness, const std::vector<int>& clause, const std::vector<int64_t>& antecedents) override;

  // When a clause is deleted, we can remove its id from the internal data structures if it has not been used in the
  // derivation of any other non-deleted clause.
  void delete_clause(int64_t id, bool redundant, const std::vector<int>& clause) override;

  // This is called upon deriving a clause consisting of the negation of a core of failing assumptions/constraints.
  // Handled just like adding a derived clause.
  void add_assumption_clause(int64_t, const std::vector<int> &, const std::vector<int64_t> &) override;

  // When a proof of unsatisfiability has been found, we want to start interpolating from the final clause,
  // or return a trivial interpolant if the formula for the definability check itself is unsatisfiable.
  void conclude_unsat(CaDiCaL::ConclusionType type, const std::vector<int64_t>& clause_ids) override;

  std::pair<int, std::vector<std::vector<int>>> get_interpolant_clauses(const std::vector<int>& shared_variables, int auxiliary_variable_start, bool rewrite_aig);

  void delete_clauses();

 private:
  // Proofnodes represent (binary) resolvents in the proof DAG.
  // The label is the literal that is resolved upon, and the left and right children are the antecedents.
  struct binary_proofnode {
    int label;
    bool flag;
    std::shared_ptr<binary_proofnode> left;
    std::shared_ptr<binary_proofnode> right;
    // Constructors
    binary_proofnode(int label, const std::shared_ptr<binary_proofnode>& left, const std::shared_ptr<binary_proofnode>& right) : label(label), flag(false), left(left), right(right) {}
    binary_proofnode(int label) : label(label), flag(false), left(nullptr), right(nullptr) {}
  };

  // Derivation nodes are created for garbage collection.
  // When a clause is no longer referenced in the derivation DAG, its data can be deleted.
  struct clause_derivation_node {
    int64_t clause_id;
    definability_interpolator& interpolator;
    std::vector<std::shared_ptr<clause_derivation_node>> antecedents;
    // Constructor
    clause_derivation_node(int64_t clause_id, definability_interpolator& interpolator) : clause_id(clause_id), interpolator(interpolator) {}
    // Destructor
    ~clause_derivation_node() {
      interpolator.delete_clause(clause_id);
    }
  };

  std::vector<int64_t> get_core() const;
  uint8_t mark_literal(int literal);
  void unmark_all();
  void create_derived_proofnode(int64_t id);
  void create_core_proofnodes();
  void process_node(const std::shared_ptr<binary_proofnode>& proofnode, std::unordered_map<std::shared_ptr<binary_proofnode>, abc::Aig_Obj_t*>& proofnode_to_aig_node, std::unordered_map<int, abc::Aig_Obj_t*>& variable_to_ci, std::vector<int>& aig_input_variables, std::unordered_set<int>& shared_variables_set);
  std::vector<int> construct_aig(const std::vector<int>& shared_variables);
  void clear_proofnodes();
  void delete_clause(int64_t id);

  int64_t empty_id;
  std::unordered_set<int> first_part_variables_set;
  std::unordered_map<int64_t, std::vector<int64_t>> clause_id_to_antecedents;
  std::unordered_map<int64_t, std::vector<int>> clause_id_to_clause;
  std::unordered_map<int64_t, std::shared_ptr<binary_proofnode>> clause_id_to_proofnode;

  std::vector<int64_t> delete_ids;
  std::unordered_map<int64_t, std::shared_ptr<clause_derivation_node>> clause_id_to_derivation_node;
  
  std::vector<int> marking_history;
  std::unordered_map<int, uint8_t> marks;

  abc::Aig_Man_t* aig_man;
};

} // namespace definability_interpolation

#endif // DEFINABILITY_INTERPOLATOR_HPP