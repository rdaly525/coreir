#include "coreir.h"
#include "coreir-passes/analysis/helloa.h"

using namespace CoreIR;

std::string Passes::HelloA::ID = "helloa";
bool Passes::HelloA::runOnNamespace(Namespace* ns) {
  cout << "Running HelloA :)" << endl;
  this->str = "ALIVEBEEF";
  return false;
}

Pass* Passes::registerHelloA() {
  return new HelloA;
}

