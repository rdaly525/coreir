#include "coreir.h"
#include "coreir/passes/analysis/verify_canonical.h"
#include "coreir/tools/cxxopts.h"

using namespace std;
using namespace CoreIR;

string Passes::VerifyCanonical::ID = "verify_canonical";

// Things to check
// all select paths are of exactly length 2 in connections

bool Passes::VerifyCanonical::runOnModule(Module* m) {
  // Check if all ports are connected for everything.
  //Context* c = this->getContext();
  ModuleDef* def = m->getDef();
 
  for (auto conn : def->getConnections()) {
    // All selects are a single select
    ASSERT(conn.first->getSelectPath().size()==2, toString(conn.first->getSelectPath()) );
    ASSERT(conn.second->getSelectPath().size()==2, toString(conn.second->getSelectPath()) );
  }
  return false;

}
