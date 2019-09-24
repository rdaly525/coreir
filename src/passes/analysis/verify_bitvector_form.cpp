#include "coreir.h"
#include "coreir/passes/analysis/verify_bitvector_form.h"
#include "coreir/tools/cxxopts.h"

using namespace std;
using namespace CoreIR;

string Passes::VerifyBitvectorForm::ID = "verify_bitvector_form";


// Things to check
// All interfaces are BitVectors (verify flattend types)
// All instances are CoreIR/not black box (verify coreir prims)
// All connections are either single bit or array of bits
// All selects are a single select

bool isBitVectorOrBit(Type* type) {
  if (auto at = dyn_cast<ArrayType>(type)) {
    return at->getElemType()->isBaseType();
  }
  return type->isBaseType();
}

bool Passes::VerifyBitvectorForm::runOnModule(Module* m) {
  // Check if all ports are connected for everything.
  //Context* c = this->getContext();
  ModuleDef* def = m->getDef();
 
  bool error = false;
  
  for (auto conn : def->getConnections()) {
    // All selects are a single select
    error |= (conn.first->getSelectPath().size() == 2);
    error |= (conn.second->getSelectPath().size() == 2);
    
    // All connections are either single bit or multi bit
    error |= isBitVectorOrBit(conn.first->getType());
  }
  
  return false;

}
