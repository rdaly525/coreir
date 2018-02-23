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
    for (auto& conn : def->getConnections()) {
      auto unpacked = unpackConnection(conn);

      toDelete.push_back(conn);

      for (auto& connR : unpacked) {
        def->connect(connR.first, connR.second);
      }
    }
    for (auto conn : toDelete) {
      def->disconnect(conn);
    }

    return true;
  }

}


bool Passes::UnpackConnections::runOnModule(Module* m) {
  return unpackConnections(m);
}
