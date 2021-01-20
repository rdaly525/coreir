#include "coreir/passes/transform/markdirty.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

bool Passes::MarkDirty::runOnContext(Context* c) {
  // Always return modified
  return true;
}
