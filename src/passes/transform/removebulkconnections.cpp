#include "coreir.h"
#include "coreir/passes/transform/removebulkconnections.h"

using namespace std;
using namespace CoreIR;

namespace {
inline bool isBit(Type* t) {
  return isa<BitType>(t) || isa<BitInType>(t) || isa<NamedType>(t);
}
bool isBitOrArrOfBits(Type* t) {
  if (isBit(t)) return true;
  if (auto at = dyn_cast<ArrayType>(t)) {
    return isBit(at->getElemType());
  }
  return false;
}
}
string Passes::RemoveBulkConnections::ID = "removebulkconnections";
bool Passes::RemoveBulkConnections::runOnModule(Module* m) {
  if (!m->hasDef()) return false;
  ModuleDef* def = m->getDef();
  
  //Naive slow way of implementing this:
  bool modified = false;
  bool hasChanged = true;
  while (hasChanged) {
    hasChanged = false;
    //Loop through all connections
    vector<Connection> toRemove;
    for (auto con : def->getConnections()) {
      Type* t = con.first->getType();
      if (isBitOrArrOfBits(t)) continue;

      //Need to disconnect and reconnect all the selects
      modified = true;
      hasChanged = true;
      toRemove.push_back(con);
      //For Arrays just connect each member of the array
      //For Record connect each field
      if (auto at = dyn_cast<ArrayType>(t)) {
        for (uint i=0; i<at->getLen(); ++i) {
          def->connect(con.first->sel(i),con.second->sel(i));
        }
      }
      else if (auto rt = dyn_cast<RecordType>(t)) {
        for (auto field : rt->getFields()) {
          def->connect(con.first->sel(field),con.second->sel(field));
        }
      }
      else {
        assert(0);
      }

    } //End for connections
    //Now need to remove all modified connections
    for (auto con : toRemove) {
      def->disconnect(con);       
    }
  }
  return modified;

}
