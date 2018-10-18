#include "coreir.h"
#include "coreir/passes/transform/cullzexts.h"

using namespace std;
using namespace CoreIR;

int main() {

  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 16;

  Type* inType = c->Record({
      {"in", c->BitIn()->Arr(width)},
        {"out", c->Bit()->Arr(width)}
    });

  Module* cl = g->newModuleDecl("cl", inType);
  ModuleDef* def = cl->newModuleDef();

  def->addInstance("neg0", "coreir.not", {{"width", Const::make(c, width)}});
  def->addInstance("zext0", "coreir.zext", {{"width_in", Const::make(c, width)},
        {"width_out", Const::make(c, width)}});

  def->connect("self.in", "zext0.in");
  def->connect("zext0.out", "neg0.in");
  def->connect("neg0.out", "self.out");

  cl->setDef(def);

  c->runPasses({"rungenerators"});
  
  assert(cl->getDef()->getInstances().size() == 2);

  c->runPasses({"cullzexts"});


  //TODO: Reintroduce when cullzexts using passthroughs
  assert(cl->getDef()->getInstances().size() == 1);

  SimulatorState state(cl);
  state.setValue("self.in", BitVec(12, 34534));

  state.execute();

  assert(state.getBitVec("self.out") == ~BitVec(12, 34534));
  deleteContext(c);

}
