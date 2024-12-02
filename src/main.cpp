#include <iostream>
#include <vector>
#include <string>
#include <iomanip>

#include "aig/aig/aig.h"
#include "base/abc/abc.h"
#include "opt/dar/dar.h"

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
  std::string filename(argv[1]);
  try {
    auto [num_variables, variables, is_existential, clauses] = parseQDIMACS(filename);

    definability_interpolation::definition_extractor extractor;
    extractor.append_formula(clauses);
    std::vector<int> defining_variables;
    int nr_defined = 0;
    int nr_existential = 0;

    for (int i=0; i < variables.size(); i++) {
      displayProgress(static_cast<double>(i+1) / static_cast<double>(num_variables));
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
    std::cout << std::endl;
    std::cout << "Number of defined existential variables: " << nr_defined << "/" << nr_existential << std::endl;
  }
  catch (FileDoesNotExistException& e) {
    std::cout << e.what() << std::endl;
    return 1;
  }

  return 0;
}
