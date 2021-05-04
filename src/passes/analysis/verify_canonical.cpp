#include "coreir.h"
#include "coreir/passes/analysis/verify_canonical.h"
#include "coreir/tools/cxxopts.h"
#include "coreir/ir/types.h"

namespace CoreIR {

std::string Passes::VerifyCanonical::ID = "verify_canonical";

// This pass checks the following:
// There are no selects on bitvectors
// There are no bundle type connections
bool Passes::VerifyCanonical::runOnModule(Module* m) {
  ModuleDef* def = m->getDef();
 
  for (auto &[a, b] : def->getConnections()) {
    ASSERT(a->getType()->isInput() || a->getType()->isOutput(), "Connections cannot be mixed type");
    for (auto w : {a, b}) {
      auto sp = w->getSelectPath();
      sp.pop_back();
      ASSERT(!isBitVector(def->sel(sp)->getType()), "Cannot select from bitvector" + toString(w->getSelectPath()));
    }
  }
  return false;
}

}  // namespace CoreIR
