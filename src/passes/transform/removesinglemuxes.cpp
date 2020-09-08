#include "coreir/passes/transform/removesinglemuxes.h"
#include "coreir/common/util.h"

using namespace std;
using namespace CoreIR;

namespace CoreIR {

namespace Passes {

bool RemoveSingleMuxes::runOnModule(Module* m) {
  if (!m->hasDef()) { return false; }

  cout << "Processing module " << m->getName() << endl;

  ModuleDef* def = m->getDef();

  bool modified = false;

  vector<Instance*> singleMuxes;
  vector<Instance*> selects;
  vector<int> del_sel;

  for (auto instR : def->getInstances()) {
    auto inst = instR.second;

    if (getQualifiedOpName(*inst) == "commonlib.muxn") {
      int n = inst->getModuleRef()->getGenArgs().at("N")->get<int>();
      modified = true;
      if (n == 1) {
        singleMuxes.push_back(inst);

        // get downstream connection
        auto out = getReceiverConnections(inst).back();
        auto down = out.second;

        // switch down connection if necessary
        if (out.second->getTopParent() == inst) { down = out.first; }

        // should only have two connections
        for (auto conn : getSourceConnections(inst)) {
          if (
            ((Select*)(conn.first))->getSelStr() != "sel" &&
            ((Select*)(conn.second))->getSelStr() != "sel") {
            // upstream connection
            auto up = conn.first;
            if (conn.first->getTopParent() == inst) { up = conn.second; }
            // connect upstream and downstream
            def->connect(up, down);
          }
          else {
            // get instance used for select signal
            if (((Select*)(conn.first))->getSelStr() == "sel") {
              selects.push_back((Instance*)(conn.second->getTopParent()));
              del_sel.push_back(0);
            }
            else if (((Select*)(conn.second))->getSelStr() == "sel") {
              selects.push_back((Instance*)(conn.first->getTopParent()));
              del_sel.push_back(0);
            }
          }
        }
      }
    }
  }

  // make sure selects aren't used elsewhere
  for (auto instR : def->getInstances()) {
    auto inst = instR.second;
    for (uint i = 0; i < selects.size(); i++) {
      auto sel = selects[i];
      if (sel == inst) del_sel[i]++;
    }
  }

  for (auto mux : singleMuxes) { def->removeInstance(mux); }
  for (uint i = 0; i < selects.size(); i++) {
    if (del_sel[i] == 1) def->removeInstance(selects[i]);
  }

  return modified;
}
}  // namespace Passes
}  // namespace CoreIR
