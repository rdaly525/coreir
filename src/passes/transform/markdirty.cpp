#include "coreir.h"
#include "coreir/passes/transform/markdirty.h"

using namespace std;
using namespace CoreIR;

bool Passes::MarkDirty::runOnContext(Context* c) {
  //Always return modified
  return true;
}

