#include "coreir.h"
#include "coreir-passes/analysis/helloa.hpp"

using namespace CoreIR;

Passes::HelloA::runOnNamespace(Namespace* ns) {
  cout << "Running HelloA" << endl;
  this->str = "HelloATester";
}
