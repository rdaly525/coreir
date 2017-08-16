
#include "coreir.h"
#include "coreir-passes/transform/hellot.hpp"
#include "coreir-passes/analysis/helloa.hpp"

using namespace CoreIR;

std::string Passes::HelloT::ID = "hellot";
bool Passes::HelloT::runOnNamespace(Namespace* ns) {
  cout << "Running HelloT" << endl;
  HelloA* dp = getAnalysisPass<HelloA>();
  cout << "Dependent pass is: " << dp->getString() << endl;
  return false;
}

Pass* Passes::registerHelloT() {
  return new HelloT;
}

