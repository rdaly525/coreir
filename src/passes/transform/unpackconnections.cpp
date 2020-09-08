#include "coreir/passes/transform/unpackconnections.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

namespace CoreIR {

bool unpackConnections(CoreIR::Module* const mod) {
  if (!mod->hasDef()) { return false; }

  ModuleDef* def = mod->getDef();
  vector<Connection> toDelete;
  vector<Connection> toConnect;

  for (auto& conn : def->getConnections()) {
    auto unpacked = unpackConnection(conn);

    toDelete.push_back(conn);

    for (auto& connR : unpacked) {
      if (!def->hasConnection(connR.first, connR.second)) {
        // def->connect(connR.first, connR.second);
        toConnect.push_back({connR.first, connR.second});
      }
    }
  }
  for (auto conn : toDelete) { def->disconnect(conn); }
  for (auto conn : toConnect) { def->connect(conn.first, conn.second); }

  return true;
}

}  // namespace CoreIR

bool Passes::UnpackConnections::runOnModule(Module* m) {
  return unpackConnections(m);
}
