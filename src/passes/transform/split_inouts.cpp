#include "coreir.h"
#include "coreir/passes/transform/split_inouts.h"

using namespace std;
using namespace CoreIR;

bool Passes::SplitInouts::runOnInstanceGraphNode(InstanceGraphNode& node) {
  return false;
}
