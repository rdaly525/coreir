#include "coreir.h"

using namespace std;
using namespace CoreIR;

void testBasicSubCircuit() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 16;

  Type* clType = c->Record({
      {"clk", c->BitIn()},
        {"in0", c->BitIn()->Arr(width)},
          {"in1", c->BitIn()->Arr(width)},
            {"config_bit", c->BitIn()},
              {"out", c->Bit()->Arr(width)}
    });

  Module* cl = g->newModuleDecl("cl", clType);
  ModuleDef* def = cl->newModuleDef();

  def->addInstance("config_reg", "corebit.dff");
  def->addInstance("toClk",
                   "coreir.wrap",
                   {{"type", Const::make(c, c->Named("coreir.clk"))}});
  def->addInstance("config_mux", "coreir.mux", {{"width", Const::make(c, width)}});

  def->connect("self.clk", "toClk.in");
  def->connect("toClk.out", "config_reg.clk");
  def->connect("self.config_bit", "config_reg.in");

  def->connect("config_reg.out", "config_mux.sel");
  def->connect("self.in0", "config_mux.in0");
  def->connect("self.in1", "config_mux.in1");
  def->connect("config_mux.out", "self.out");

  cl->setDef(def);

  c->runPasses({"rungenerators"});

  auto subCircuitInstances =
    extractSubcircuit(cl, {def->sel("self")->sel("clk"),
          def->sel("self")->sel("config_bit")});

  cout << "Size of subciruit = " << subCircuitInstances.size() << endl;

  assert(subCircuitInstances.size() == 2);
}

int main() {
  testBasicSubCircuit();
}
