#include "coreir.h"
#include "coreir/simulator/interpreter.h"

using namespace CoreIR;
using namespace std;

Module* randomCircuit(CoreIR::Context* c,
                      CoreIR::Namespace* g,
                      const int numInputs,
                      const int numOutputs,
                      const int numOperations,
                      const std::string& moduleName) {
  RecordParams params;

  // Add inputs and outputs
  

  Type* modType = c->Record(params);

  Module* mod = g->newModuleDecl(moduleName, modType);

  ModuleDef* def = mod->newModuleDef();

  // Create value here

  // Done

  mod->setDef(def);

  return mod;
}
