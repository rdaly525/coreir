#include "coreir.h"
#include "coreir/passes/transform/unpackconnections.h"

using namespace std;
using namespace CoreIR;


namespace CoreIR {
//Do not forget to set this static variable!!
string Passes::UnpackConnections::ID = "unpackconnections";

  bool unpackConnections(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();
    vector<Connection> toDelete;
    vector<Connection> toConnect;

    for (auto& conn : def->getConnections()) {
      auto unpacked = unpackConnection(conn);

      toDelete.push_back(conn);

      for (auto& connR : unpacked) {
        if (!def->hasConnection(connR.first,connR.second)) {
          //def->connect(connR.first, connR.second);
          toConnect.push_back({connR.first, connR.second});
        }
      }
    }
    for (auto conn : toDelete) {
      def->disconnect(conn);
    }
    for (auto conn : toConnect) {
      def->connect(conn.first, conn.second);
    }

    return true;
  }

}


bool Passes::UnpackConnections::runOnModule(Module* m) {
  return unpackConnections(m);
}
