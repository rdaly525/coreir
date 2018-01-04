#include "coreir.h"
#include "coreir/passes/transform/clockifyinterface.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 8;

  Type* clType = c->Record({
      {"clk", c->BitIn()},
        {"in", c->BitIn()->Arr(width)},
          {"out", c->Bit()->Arr(width)}
    });

  Module* cl = g->newModuleDecl("cl", clType);
  ModuleDef* def = cl->newModuleDef();

  def->addInstance("reg0",
                   "coreir.reg",
                   {{"width", Const::make(c, width)}});

  def->connect("self.in", "reg0.in");

  // Add clock cast node, in rtlil the clock input is just another bit
  //def->addInstance("toClk0", "rtlil.to_clkIn");
  def->addInstance("toClk0",
                   "coreir.wrap",
                   {{"type", Const::make(c, c->Named("coreir.clk"))}});

  def->connect("self.clk", "toClk0.in");
  def->connect("toClk0.out", "reg0.clk");

  def->connect("reg0.out", "self.out");
  
  cl->setDef(def);

  c->runPasses({"rungenerators", "clockifyinterface"});

  // clockification deletes the cast to clock
  assert(cl->getDef()->getInstances().size() == 1);

  deleteContext(c);
}
