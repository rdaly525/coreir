
#include "coreir.h"
#include "coreir-passes/transform/hellot.h"
#include "coreir-passes/analysis/helloa.h"

using namespace CoreIR;

std::string Passes::HelloT::ID = "hellot";
bool Passes::HelloT::runOnNamespace(Namespace* ns) {
  cout << "Running HelloT" << endl;
  HelloA* dp = getAnalysisPass<HelloA>();
  cout << "Dependent pass is: " << dp->getString() << endl;
  return false;
}
