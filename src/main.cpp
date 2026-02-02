#include <iostream>
#include <vector>
#include <string>
#include <iomanip>
#include <set>
#include <unordered_map>
#include <unordered_set>
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

  CLI11_PARSE(app, argc, argv);

  try {
    auto [num_variables, variables, is_existential, clauses] = parseQDIMACS(filename);

    definability_interpolation::definition_extractor extractor;
    extractor.append_formula(clauses);
    int nr_defined = 0;
    int nr_existential = 0;

    if (basic) {
      // Original forward-order strategy: iterate variables in QDIMACS order,
      // accumulating defining variables as we go.
      std::vector<int> defining_variables;
      for (int i = 0; i < variables.size(); i++) {
        displayProgress(static_cast<double>(i + 1) / static_cast<double>(num_variables));
        auto v = variables[i];
        if (is_existential[i]) {
          nr_existential++;
          if (extractor.has_definition(v, defining_variables, {})) {
            nr_defined++;
            extractor.get_definition(false);
          }
        }
        defining_variables.push_back(v);
      }
    } else {
      // Reverse-order strategy with transitive support checking.
      std::unordered_set<int> universal_vars;
      std::unordered_set<int> existential_vars;
      for (int i = 0; i < variables.size(); i++) {
        if (is_existential[i]) existential_vars.insert(variables[i]);
        else universal_vars.insert(variables[i]);
      }

      std::unordered_set<int> defined_existentials;
      std::unordered_map<int, std::set<int>> transitive_support;

      for (int i = variables.size() - 1; i >= 0; i--) {
        displayProgress(static_cast<double>(variables.size() - i) / static_cast<double>(num_variables));
        auto y = variables[i];
        if (!is_existential[i]) continue;

        nr_existential++;

        // Build defining_variables for y:
        // - All universal variables
        // - Undefined existential variables (excluding y)
        // - Defined existential x only if y is NOT in transitive_support[x]
        std::vector<int> defining_variables;
        for (auto u : universal_vars) {
          defining_variables.push_back(u);
        }
        for (auto e : existential_vars) {
          if (e == y) continue;
          if (defined_existentials.count(e)) {
            if (transitive_support[e].count(y) == 0) {
              defining_variables.push_back(e);
            }
          } else {
            defining_variables.push_back(e);
          }
        }

        if (extractor.has_definition(y, defining_variables, {})) {
          nr_defined++;
          auto [definition_clauses, aux_start] = extractor.get_definition(false);

          // Compute direct support: defining variables appearing in the definition clauses.
          std::set<int> defining_set(defining_variables.begin(), defining_variables.end());
          std::set<int> direct_support;
          for (const auto& clause : definition_clauses) {
            for (int lit : clause) {
              int var = abs(lit);
              if (var != y && defining_set.count(var)) {
                direct_support.insert(var);
              }
            }
          }

          // Compute transitive support: direct_support ∪ transitive supports of defined vars in direct_support.
          std::set<int> t_support = direct_support;
          for (int z : direct_support) {
            if (transitive_support.count(z)) {
              t_support.insert(transitive_support[z].begin(), transitive_support[z].end());
            }
          }

          defined_existentials.insert(y);
          transitive_support[y] = t_support;
        }
      }
    }

    std::cout << std::endl;
    std::cout << "Number of defined existential variables: " << nr_defined << "/" << nr_existential << std::endl;
  }
  catch (FileDoesNotExistException& e) {
    std::cout << e.what() << std::endl;
    return 1;
  }

  return 0;
}
