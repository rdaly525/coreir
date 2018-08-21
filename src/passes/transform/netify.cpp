#include "coreir.h"
#include "coreir/passes/transform/netify.h"

using namespace std;
using namespace CoreIR;

string Passes::Netify::ID = "netify";

namespace CoreIR {
namespace Passes {
  
  //Take all connections and a coreir-wire into it
  bool Passes::Netify::runOnModule(Module* m) {
    Context* c = getContext();
    ModuleDef* def = m->getDef();
    vector<Connection> toRemove;
    for (auto conn : def->getConnections()) {
      Wireable* wa = conn.first;
      Wireable* wb = conn.second;

      //First check if either end is an io port or a coreir wire
      //if so, then do not need to add a wire
      Wireable* waTop = wa->getTopParent();
      Wireable* wbTop = wb->getTopParent();
      if (isa<Interface>(waTop) || isa<Interface>(wbTop)) {
        continue;
      }
      string aModKind = cast<Instance>(waTop)->getModuleRef()->getRefName();
      string bModKind = cast<Instance>(wbTop)->getModuleRef()->getRefName();
      if (aModKind == "coreir.wire" || aModKind == "corebit.wire") {
        continue;
      }
      if (bModKind == "coreir.wire" || bModKind == "corebit.wire") {
        continue;
      }

      //Both ends of the connection are instances
      Type* wtype = wa->getType();
      ASSERT(!wtype->isInOut() && !wtype->isMixed(),"NYI");
      Instance* wire;
      if (auto at = dyn_cast<ArrayType>(wtype)) {
        int len = at->getLen();
        auto spa = wa->getSelectPath();
        auto spb = wb->getSelectPath();
        string wire_name = join(spa.begin(),spa.end(),string("_")) + "__" + join(spb.begin(),spb.end(),string("_"));
        wire = def->addInstance("wire" + c->getUnique(),"coreir.wire",{{"width",Const::make(c,len)}});
      }
      else {
        ASSERT(wtype->isBaseType(),"Cannot handle non-base types");
        wire = def->addInstance("wire" + c->getUnique(),"corebit.wire");
      }

      if (wa->getType()->isInput()) {
        def->connect(wa,wire->sel("out"));
        def->connect(wb,wire->sel("in"));
      }
      else {
        def->connect(wa,wire->sel("in"));
        def->connect(wb,wire->sel("out"));
      }
      toRemove.push_back(conn);
    }
    for (auto conn : toRemove) {
      def->disconnect(conn);
    }
    return toRemove.size()>0;
  }

}
}
