#include "coreir.h"
#include "coreir/passes/transform/markdirty.h"

using namespace std;
using namespace CoreIR;

string Passes::MarkDirty::ID = "markdirty";
bool Passes::MarkDirty::runOnContext(Context* c) {
  //Always return modified
  return true;
}

