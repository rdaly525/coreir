#include "coreir/passes/transform/removeunconnected.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

namespace {
bool hasConnection(Wireable* w) {
  if (w->getConnectedWireables().size()) return true;

  for (auto smap : w->getSelects()) {
    if (hasConnection(smap.second)) return true;
  }
  return false;
}
}  // namespace

bool Passes::RemoveUnconnected::runOnInstance(Instance* i) {
  if (!hasConnection(i)) {
    i->getContainer()->removeInstance(i);
    return true;
  }
  return false;
}
