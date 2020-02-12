#include "coreir.h"
#include "coreir/passes/transform/flatten.h"

using namespace std;
using namespace CoreIR;

bool Passes::Flatten::runOnInstanceGraphNode(InstanceGraphNode& node) {
  bool changed = false;
  //int i = 0;
  for (auto inst : node.getInstanceList()) {
    //cout << "inlining " << i++ << endl;
    changed |= inlineInstance(inst);
  }
  return changed;
}
