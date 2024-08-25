#include "klee/ADT/Ref.h"

#include "klee/Coq/CoqLanguage.h"

//#include <iostream>
#include <string>
#include <sstream>

using namespace std;
using namespace klee;

string CoqExpr::dump() const {
  assert(false);
}

CoqVariable::CoqVariable(string name) : name(name) {

}

string CoqVariable::dump() const {
  return name;
}

CoqApplication::CoqApplication(const ref<CoqExpr> &function,
                               const std::vector<ref<CoqExpr>> &args) :
    function(function), args(args) {

}

string CoqApplication::dump() const {
  std::ostringstream os;

  os << "(";
  os << function->dump();
  os << " ";

  for (size_t i = 0; i < args.size(); i++) {
    if (i != 0) {
      os << " ";
    }
    os << args[i]->dump();
  }

  os << ")";

  return os.str();
}

CoqList::CoqList(const std::vector<ref<CoqExpr>> &args) :
    args(args) {

}

string CoqList::dump() const {
  std::ostringstream os;

  os << "[";

  for (size_t i = 0; i < args.size(); i++) {
    if (i != 0) {
      os << "; ";
    }
    os << args[i]->dump();
  }

  os << "]";

  return os.str();
}
