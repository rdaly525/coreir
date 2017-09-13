#include "coreir.h"
#include "coreir-passes/transform/removeunconnected.h"

using namespace CoreIR;

namespace {
bool hasConnection(Wireable* w) {
  if (w->getConnectedWireables().size()) return true;
  
  bool hasCon = false;
  for (auto smap : w->getSelects()) {
    hasCon |= hasConnection(smap.second);
  }
  return hasCon;
}
}

string Passes::RemoveUnconnected::ID = "removeunconnected";
bool Passes::RemoveUnconnected::runOnInstance(Instance* i) {
  if (!hasConnection(i)) {
    i->getContainer()->removeInstance(i);
    return true;
  }
  return false;
}
