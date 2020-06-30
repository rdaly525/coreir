#include "coreir/passes/transform/markdirty.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

string Passes::MarkDirty::ID = "markdirty";
bool Passes::MarkDirty::runOnContext(Context* c) {
  // Always return modified
  return true;
}
