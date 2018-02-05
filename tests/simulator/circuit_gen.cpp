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
  // TODO: Make this a parameter
  uint width = 16;
  
  RecordParams params;

  // Add inputs and outputs
  for (int i = 0; i < numInputs; i++) {
    params.push_back({"in_" + to_string(i), c->Array(width, c->BitIn())});
  }

  for (int i = 0; i < numOutputs; i++) {
    params.push_back({"out_" + to_string(i), c->Array(width, c->Bit())});
  }
  
  Type* modType = c->Record(params);

  Module* mod = g->newModuleDecl(moduleName, modType);

  ModuleDef* def = mod->newModuleDef();

  // Add instances to definition

  Generator* and2 = c->getGenerator("coreir.and");
  Generator* or2 = c->getGenerator("coreir.or");
  
  for (int i = 0; i < numOperations; i++) {
    //Wireable* op;
    if ((i % 2) == 0) {
      //op =
        def->addInstance("op_" + to_string(i), and2, {{"width", Const::make(c, width)}});
    } else {
      //op =
        def->addInstance("op_" + to_string(i), or2, {{"width", Const::make(c, width)}});
    }

  }

  // Done

  mod->setDef(def);

  return mod;
}
