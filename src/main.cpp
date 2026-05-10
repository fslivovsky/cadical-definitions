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
            auto [def_clauses, aux_start] = extractor.get_definition(false);
            total_definition_clauses += def_clauses.size();
            if (write_definitions) {
              all_definition_clauses.insert(all_definition_clauses.end(),
                std::make_move_iterator(def_clauses.begin()),
                std::make_move_iterator(def_clauses.end()));
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
    std::cout << "Total number of definition clauses: " << total_definition_clauses << std::endl;

    if (write_definitions) {
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
