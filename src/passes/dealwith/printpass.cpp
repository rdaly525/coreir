#include "coreir.h"
#include "coreir-passes/printpass.hpp"

using namespace CoreIR;

bool PrintPass::runOnNamespace(Namespace* ns) {
  cout << "PRINT PASS!" << endl;
  ns->print();
  cout << "DONE PRINT PASS!" << endl;
  return false;
}

