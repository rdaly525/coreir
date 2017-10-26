#include "coreir.h"
#include "coreir/passes/analysis/createinstancegraph.h"

using namespace CoreIR;
using namespace std;

std::string Passes::CreateInstanceGraph::ID = "createinstancegraph";
bool Passes::CreateInstanceGraph::runOnContext(Context* c) {
  ig->construct(c);
  return false;
}
void Passes::CreateInstanceGraph::releaseMemory() {
  ig->releaseMemory();
}
