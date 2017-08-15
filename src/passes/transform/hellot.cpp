
#include "coreir.h"
#include "coreir-passes/analysis/helloa.hpp"

using namespace CoreIR;

Passes::HelloT::runOnNamespace(Namespace* ns) {
  cout << "Running HelloT" << endl;
  getAnalaysisPass<HelloA>
}
