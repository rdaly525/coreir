#include "coreir.h"
#include "coreir/passes/transform/flatten.h"

using namespace std;
using namespace CoreIR;

string Passes::Flatten::ID = "flatten";
bool Passes::Flatten::runOnInstanceGraphNode(InstanceGraphNode& node) {
  cout << "inlining all " << node.getModule()->toString() << endl;
  cout << "number of instances = " << node.getInstanceList().size() << endl;
  bool changed = false;
  //int i = 0;
  for (auto inst : node.getInstanceList()) {
    //cout << "inlining " << i++ << endl;
    changed |= inlineInstance(inst);
  }

  cout << "Done flattening" << endl;
  return changed;
}
