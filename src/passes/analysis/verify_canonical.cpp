#include "coreir.h"
#include "coreir/passes/analysis/verify_canonical.h"
#include "coreir/tools/cxxopts.h"

namespace CoreIR {

std::string Passes::VerifyCanonical::ID = "verify_canonical";

// This pass checks the following:
// -- All select paths are of exactly length 2 in connections
bool Passes::VerifyCanonical::runOnModule(Module* m) {
  ModuleDef* def = m->getDef();
 
  for (auto conn : def->getConnections()) {
    // Check that all selects are of depth 1.
    ASSERT(conn.first->getSelectPath().size() == 2,
           toString(conn.first->getSelectPath()));
    ASSERT(conn.second->getSelectPath().size() == 2,
           toString(conn.second->getSelectPath()));
  }
  return false;
}

}  // namespace CoreIR
