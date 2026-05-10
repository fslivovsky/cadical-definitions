#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <iomanip>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <cstdlib>

#include "aig/aig/aig.h"
#include "base/abc/abc.h"
#include "opt/dar/dar.h"

#include <CLI/CLI.hpp>

#include "qdimacs.hpp"
#include "definition_extractor.hpp"

using namespace abc; // Needed for ABC iteration macros.

using definability_interpolation::AigWithInputs;

void displayProgress(double progress) {
  int barWidth = 70;

  std::cout << "[";
  int pos = static_cast<int>(barWidth * progress);
  for (int i = 0; i < barWidth; ++i) {
      if (i < pos) std::cout << "=";
      else if (i == pos) std::cout << ">";
      else std::cout << " ";
  }
  std::cout << "] " << std::setprecision(1) << std::fixed << progress * 100.0 << "%\r";
  std::cout.flush();
}

int main(int argc, char** argv) {
  CLI::App app{"Find propositional definitions of existential variables"};

  std::string filename;
  app.add_option("input", filename, "QDIMACS input file")->required();

  bool basic = false;
  app.add_flag("--basic", basic, "Use basic forward-order strategy");

  bool strict = false;
  app.add_flag("--strict", strict, "With --basic: only add an existential to the support if it was defined (transitively) by the universal variables");

  std::string write_definitions_path;
  app.add_option("--write-definitions", write_definitions_path, "Write all definition clauses to a DIMACS file at the given path");

  CLI11_PARSE(app, argc, argv);

  bool write_definitions = !write_definitions_path.empty();

  try {
    auto [num_variables, variables, is_existential, clauses] = parseQDIMACS(filename);

    definability_interpolation::definition_extractor extractor;
    extractor.append_formula(clauses);
    int nr_defined = 0;
    int nr_existential = 0;
    std::vector<std::vector<int>> all_definition_clauses;

    size_t total_definition_clauses = 0;

    // Under --basic --strict: collect per-variable AIGs in defined order
    // (insertion order is a valid topological order because we only add
    // variables to the support after they have been shown to be definable).
    std::vector<std::pair<int, AigWithInputs>> defined_aigs;

    if (basic) {
      // Original forward-order strategy: iterate variables in QDIMACS order,
      // accumulating defining variables as we go.
      std::vector<int> defining_variables;
      for (int i = 0; i < variables.size(); i++) {
        displayProgress(static_cast<double>(i + 1) / static_cast<double>(num_variables));
        auto v = variables[i];
        bool defined = false;
        if (is_existential[i]) {
          nr_existential++;
          if (extractor.has_definition(v, defining_variables, {})) {
            nr_defined++;
            defined = true;
            if (strict) {
              // AIG path: don't compute clauses.
              AigWithInputs aig = extractor.get_definition_aig(false);
              defined_aigs.emplace_back(v, std::move(aig));
            } else {
              auto [def_clauses, aux_start] = extractor.get_definition(false);
              total_definition_clauses += def_clauses.size();
              if (write_definitions) {
                all_definition_clauses.insert(all_definition_clauses.end(),
                  std::make_move_iterator(def_clauses.begin()),
                  std::make_move_iterator(def_clauses.end()));
              }
            }
          }
        }
        if (!is_existential[i] || !strict || defined) {
          defining_variables.push_back(v);
        }
      }
    } else {
      // Reverse-order strategy with transitive support checking.
      std::unordered_set<int> universal_vars;
      std::unordered_set<int> existential_vars;
      for (int i = 0; i < variables.size(); i++) {
        if (is_existential[i]) existential_vars.insert(variables[i]);
        else universal_vars.insert(variables[i]);
      }

      // reverse_support[z] = vars whose direct support contains z.
      std::unordered_map<int, std::vector<int>> reverse_support;
      int num_variables_int = static_cast<int>(num_variables);

      for (int i = variables.size() - 1; i >= 0; i--) {
        displayProgress(static_cast<double>(variables.size() - i) / static_cast<double>(num_variables));
        auto y = variables[i];
        if (!is_existential[i]) continue;

        nr_existential++;

        // BFS from y through reverse_support to find all vars that transitively depend on y.
        std::unordered_set<int> depends_on_y;
        auto rev_it = reverse_support.find(y);
        if (rev_it != reverse_support.end()) {
          std::vector<int> queue(rev_it->second.begin(), rev_it->second.end());
          depends_on_y.insert(queue.begin(), queue.end());
          size_t idx = 0;
          while (idx < queue.size()) {
            int x = queue[idx++];
            auto it = reverse_support.find(x);
            if (it == reverse_support.end()) continue;
            for (int w : it->second) {
              if (depends_on_y.insert(w).second) {
                queue.push_back(w);
              }
            }
          }
        }

        std::vector<int> defining_variables;
        for (auto u : universal_vars) {
          defining_variables.push_back(u);
        }
        for (auto e : existential_vars) {
          if (e == y) continue;
          if (depends_on_y.count(e)) continue;
          defining_variables.push_back(e);
        }

        if (extractor.has_definition(y, defining_variables, {})) {
          nr_defined++;
          auto [definition_clauses, aux_start] = extractor.get_definition(false);
          total_definition_clauses += definition_clauses.size();

          // Compute direct support: problem variables (excluding y) appearing in the definition clauses.
          std::vector<int> support;
          for (const auto& clause : definition_clauses) {
            for (int lit : clause) {
              int var = abs(lit);
              if (var != y && var <= num_variables_int) {
                support.push_back(var);
              }
            }
          }
          std::sort(support.begin(), support.end());
          support.erase(std::unique(support.begin(), support.end()), support.end());

          for (int z : support) {
            reverse_support[z].push_back(y);
          }

          if (write_definitions) {
            all_definition_clauses.insert(all_definition_clauses.end(),
              std::make_move_iterator(definition_clauses.begin()),
              std::make_move_iterator(definition_clauses.end()));
          }
        }
      }
    }

    std::cout << std::endl;
    std::cout << "Number of defined existential variables: " << nr_defined << "/" << nr_existential << std::endl;
    if (!(basic && strict)) {
      std::cout << "Total number of definition clauses: " << total_definition_clauses << std::endl;
    }

    if (basic && strict) {
      // Build a joint AIG with universals AND defined existentials as CIs,
      // and one CO per defined existential giving its definition cone. This
      // allows sharing across definitions: if multiple defs reference y_1 or
      // share sub-circuits, those parts appear once in the joint AIG.
      Aig_Man_t* joint = Aig_ManStart(0);
      std::unordered_map<int, Aig_Obj_t*> joint_var_to_ci;
      std::unordered_map<int, Aig_Obj_t*> joint_def_node;
      std::vector<int> def_order;

      auto get_or_create_joint_ci = [&](int var) -> Aig_Obj_t* {
        auto it = joint_var_to_ci.find(var);
        if (it != joint_var_to_ci.end()) return it->second;
        Aig_Obj_t* ci = Aig_ObjCreateCi(joint);
        joint_var_to_ci[var] = ci;
        return ci;
      };

      for (auto& [y, aig] : defined_aigs) {
        if (!aig.aig_man) continue;
        def_order.push_back(y);

        Aig_ManCleanData(aig.aig_man);
        Aig_ManConst1(aig.aig_man)->pData = Aig_ManConst1(joint);

        Aig_Obj_t* pObj;
        int i;
        Aig_ManForEachCi(aig.aig_man, pObj, i) {
          int input_var = aig.input_variables[i];
          pObj->pData = get_or_create_joint_ci(input_var);
        }

        Aig_Obj_t* co = Aig_ManCo(aig.aig_man, 0);
        Aig_Obj_t* root = Aig_ObjFanin0(co);
        Aig_ManDupSimpleDfs_rec(joint, aig.aig_man, root);
        Aig_Obj_t* def_node = Aig_NotCond((Aig_Obj_t*)root->pData, Aig_ObjFaninC0(co));
        joint_def_node[y] = def_node;
        Aig_ObjCreateCo(joint, def_node);

        // Add a CI for y so subsequent defs that reference y go through this
        // shared CI; substituted with def_node at the end.
        if (!joint_var_to_ci.count(y)) {
          joint_var_to_ci[y] = Aig_ObjCreateCi(joint);
        }
      }

      int joint_ci = Aig_ManCiNum(joint);
      int joint_co = Aig_ManCoNum(joint);
      int joint_and = Aig_ManNodeNum(joint);
      std::cout << "Joint AIG (with y-inputs): " << joint_ci << " inputs, "
                << joint_co << " outputs, " << joint_and << " AND gates" << std::endl;

      // Substitute y-CIs in the joint AIG with their corresponding def cones
      // to produce the final AIG (universal-only inputs). pData memoization
      // on `joint` ensures shared sub-circuits are imported once.
      std::unordered_set<int> universal_set;
      for (int i = 0; i < (int)variables.size(); i++) {
        if (!is_existential[i]) universal_set.insert(variables[i]);
      }
      std::vector<int> ordered_universals;
      for (int i = 0; i < (int)variables.size(); i++) {
        int v = variables[i];
        if (universal_set.count(v) && joint_var_to_ci.count(v)) {
          ordered_universals.push_back(v);
        }
      }

      Aig_Man_t* final_aig = Aig_ManStart(ordered_universals.size());
      std::unordered_map<int, Aig_Obj_t*> universal_to_final_ci;
      for (int u : ordered_universals) {
        universal_to_final_ci[u] = Aig_ObjCreateCi(final_aig);
      }

      Aig_ManCleanData(joint);
      Aig_ManConst1(joint)->pData = Aig_ManConst1(final_aig);
      for (int u : ordered_universals) {
        joint_var_to_ci[u]->pData = universal_to_final_ci[u];
      }

      std::unordered_map<int, Aig_Obj_t*> final_def_node;
      for (int y : def_order) {
        Aig_Obj_t* joint_def = joint_def_node[y];
        Aig_Obj_t* joint_root = Aig_Regular(joint_def);
        Aig_ManDupSimpleDfs_rec(final_aig, joint, joint_root);
        Aig_Obj_t* final_def = Aig_NotCond((Aig_Obj_t*)joint_root->pData, Aig_IsComplement(joint_def));
        final_def_node[y] = final_def;
        // Set y-CI pData so later y_k that depend on y use the substituted cone.
        if (joint_var_to_ci.count(y)) {
          joint_var_to_ci[y]->pData = final_def;
        }
      }

      std::vector<int> output_order;
      for (int i = 0; i < (int)variables.size(); i++) {
        int v = variables[i];
        if (final_def_node.count(v)) output_order.push_back(v);
      }
      for (int v : output_order) {
        Aig_ObjCreateCo(final_aig, final_def_node[v]);
      }
      Aig_ManCleanup(final_aig);

      int num_ci = Aig_ManCiNum(final_aig);
      int num_co = Aig_ManCoNum(final_aig);
      int num_and = Aig_ManNodeNum(final_aig);
      std::cout << "Combined definition AIG: " << num_ci << " inputs, "
                << num_co << " outputs, " << num_and << " AND gates" << std::endl;

      if (write_definitions) {
        Vec_Ptr_t* vNodes = Aig_ManDfs(final_aig, 1);

        unsigned next_var = 1;
        Aig_Obj_t* pObj;
        int i;
        Aig_ManForEachCi(final_aig, pObj, i) {
          pObj->iData = next_var++;
        }
        Vec_PtrForEachEntry(Aig_Obj_t*, vNodes, pObj, i) {
          pObj->iData = next_var++;
        }
        Aig_ManConst1(final_aig)->iData = 0;
        unsigned max_var = next_var - 1;

        auto obj_to_lit = [&](Aig_Obj_t* obj, bool compl_edge) -> unsigned {
          if (Aig_ObjIsConst1(obj))
            return compl_edge ? 0u : 1u;
          return 2 * (unsigned)obj->iData + (compl_edge ? 1u : 0u);
        };

        std::ofstream out(write_definitions_path);
        if (!out) {
          std::cerr << "Error: could not open " << write_definitions_path << " for writing" << std::endl;
          Vec_PtrFree(vNodes);
          Aig_ManStop(final_aig);
          Aig_ManStop(joint);
          return 1;
        }

        out << "aag " << max_var << " " << num_ci << " 0 " << num_co << " " << num_and << "\n";
        Aig_ManForEachCi(final_aig, pObj, i) {
          out << 2 * (unsigned)pObj->iData << "\n";
        }
        Aig_ManForEachCo(final_aig, pObj, i) {
          out << obj_to_lit(Aig_ObjFanin0(pObj), Aig_ObjFaninC0(pObj)) << "\n";
        }
        Vec_PtrForEachEntry(Aig_Obj_t*, vNodes, pObj, i) {
          unsigned lhs = 2 * (unsigned)pObj->iData;
          unsigned rhs0 = obj_to_lit(Aig_ObjFanin0(pObj), Aig_ObjFaninC0(pObj));
          unsigned rhs1 = obj_to_lit(Aig_ObjFanin1(pObj), Aig_ObjFaninC1(pObj));
          out << lhs << " " << rhs0 << " " << rhs1 << "\n";
        }
        {
          int idx = 0;
          for (int v : ordered_universals) out << "i" << idx++ << " x" << v << "\n";
        }
        {
          int idx = 0;
          for (int v : output_order) out << "o" << idx++ << " y" << v << "\n";
        }

        Vec_PtrFree(vNodes);
        std::cout << "Wrote AIGER file: " << write_definitions_path << std::endl;
      }

      Aig_ManStop(final_aig);
      Aig_ManStop(joint);
    } else if (write_definitions) {
      int max_var = 0;
      for (const auto& cl : all_definition_clauses) {
        for (int lit : cl) {
          int v = std::abs(lit);
          if (v > max_var) max_var = v;
        }
      }
      std::ofstream out(write_definitions_path);
      if (!out) {
        std::cerr << "Error: could not open " << write_definitions_path << " for writing" << std::endl;
        return 1;
      }
      out << "p cnf " << max_var << " " << all_definition_clauses.size() << "\n";
      for (const auto& cl : all_definition_clauses) {
        for (int lit : cl) out << lit << " ";
        out << "0\n";
      }
    }
  }
  catch (FileDoesNotExistException& e) {
    std::cout << e.what() << std::endl;
    return 1;
  }

  return 0;
}
