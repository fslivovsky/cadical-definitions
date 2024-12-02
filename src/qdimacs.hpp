#ifndef QDIMACS_HPP_
#define QDIMACS_HPP_

#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <exception>
#include <tuple>

class FileDoesNotExistException: public std::exception {
 public:
  FileDoesNotExistException(const std::string& filename): filename(filename) {}

  const char* what() const noexcept override {
    std::string message = "File does not exist: " + filename;
    return message.c_str();
  }

 private:
  std::string filename;
};

auto parseQDIMACS(const std::string& filename) {
  std::ifstream file(filename);
  if (!file)
    throw FileDoesNotExistException(filename);

  std::string line, buffer;
  int num_variables, num_clauses;
  std::vector<int> variables;
  std::vector<bool> is_existential;
  std::vector<std::vector<int>> clauses;

  while (std::getline(file, line)) {
    if (line.empty())
      continue;
    std::istringstream iss(line);
    char ch;
    iss >> ch;
    if (ch == 'c') // Comment line
      continue;
    else if (ch == 'p') // Header line
      iss >> buffer >> num_variables >> num_clauses;
    else if (ch == 'a' || ch == 'e') { // Quantifier line
      bool existential = (ch == 'e');
      int variable;
      while (iss >> variable, variable != 0) {
        variables.push_back(variable);
        is_existential.push_back(existential);
      }
    }
    else {// Clause line
      iss.putback(ch);
      std::vector<int> clause;
      int literal;
      while(iss >> literal, literal != 0)
        clause.push_back(literal);
      clauses.push_back(clause);
    }
  }
  return std::make_tuple(num_variables, variables, is_existential, clauses);
}

#endif // QDIMACS_HPP_