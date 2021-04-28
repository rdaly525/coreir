#include "coreir/passes/analysis/createinstancegraph.h"
#include "coreir.h"

using namespace CoreIR;
using namespace std;

bool Passes::CreateInstanceGraph::runOnContext(Context* c) {
  ig->construct(c);
  return false;
}

void Passes::CreateInstanceGraph::releaseMemory() { ig->releaseMemory(); }
