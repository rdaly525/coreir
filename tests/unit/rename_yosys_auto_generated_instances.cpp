#include "coreir.h"
#include "coreirsim.h"

#include "coreir/passes/transform/rename_yosys_auto_generated_instances.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  Type* mTp = c->Record({{"in0", c->BitIn()->Arr(3)},
                         {"in1", c->BitIn()->Arr(3)},
                         {"out0", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("m", mTp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance(
    "__DOLLAR__horrible_FORWARD_SLASH_yosys_name",
    "coreir.add",
    {{"width", Const::make(c, 3)}});
  def->connect("self.in0", "__DOLLAR__horrible_FORWARD_SLASH_yosys_name.in0");
  def->connect("self.in1", "__DOLLAR__horrible_FORWARD_SLASH_yosys_name.in1");
  def->connect("__DOLLAR__horrible_FORWARD_SLASH_yosys_name.out", "self.out0");

  md->setDef(def);

  c->runPasses(
    {"rename_yosys_auto_generated_instances", "deletedeadinstances"});

  assert(md->getDef()->getInstances().size() == 1);

  cout << "Module after processing" << endl;
  md->print();

  SimulatorState sim(md);
  sim.setValue("self.in0", BitVector(3, 1));
  sim.setValue("self.in1", BitVector(3, 2));

  sim.execute();

  assert(
    sim.getBitVec("self.out0") ==
    add_general_width_bv(BitVector(3, 1), BitVector(3, 2)));

  for (auto instM : md->getDef()->getInstances()) {
    Instance* inst = instM.second;
    assert(inst->toString()[0] != '_');
  }

  deleteContext(c);
}
