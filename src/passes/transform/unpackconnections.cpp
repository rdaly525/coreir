#include "coreir.h"
#include "coreir/passes/transform/unpackconnections.h"

using namespace std;
using namespace CoreIR;


namespace CoreIR {
//Do not forget to set this static variable!!
string Passes::UnpackConnections::ID = "unpackconnections";

  std::vector<Connection>
  unpackConnection(const CoreIR::Connection& conn) {
    Wireable* fst = conn.first;
    Wireable* snd = conn.second;

    assert(fst->getType() == snd->getType()->getFlipped());

    Type* fstType = fst->getType();

    // Bit connections are already unpacked
    if ((fstType->getKind() == Type::TK_Bit) ||
        (fstType->getKind() == Type::TK_BitIn)) {
      return {conn};
    }

    if (fstType->getKind() == Type::TK_Named) {
      return {conn};
    }

    vector<Connection> unpackedConns;

    if (fstType->getKind() == Type::TK_Array) {
      ArrayType* arrTp = cast<ArrayType>(fstType);
      int len = arrTp->getLen();

      for (int i = 0; i < len; i++) {
        concat(unpackedConns, unpackConnection({fst->sel(i), snd->sel(i)}));
      }

      return unpackedConns;

    } else {
      cout << "Wireable " << fst->toString() << " has unsupported type in unpackConnection = " << fstType->toString() << endl;
      assert(false);
    }

    assert(false);
  }

  bool unpackConnections(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();

    for (auto& conn : def->getConnections()) {
      auto unpacked = unpackConnection(conn);

      def->disconnect(conn);

      for (auto& connR : unpacked) {
        def->connect(connR.first, connR.second);
      }
    }

    return true;
  }

}


bool Passes::UnpackConnections::runOnModule(Module* m) {
  return unpackConnections(m);
}
