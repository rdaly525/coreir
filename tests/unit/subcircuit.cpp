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
  for (auto inst : subCircuitInstances) {
    cout << "\t" << inst->toString() << endl;
  }

  assert(subCircuitInstances.size() == 2);

  deleteContext(c);
}

void testCGRAConfigSubcircuit() {
  Context* c = newContext();

  Module* topMod = nullptr;

  cout << "Loading CGRA" << endl;

  if (!loadFromFile(c,"/Users/dillon/VerilogWorkspace/CGRAGenerator/hardware/generator_z/top/top_flat_clk.json", &topMod)) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }

  cout << "Loaded CGRA" << endl;

  assert(topMod != nullptr);

  assert(topMod->hasDef());

  ModuleDef* def = topMod->getDef();

  auto subCircuitInstances =
    extractSubcircuit(topMod, {def->sel("self")->sel("clk"),
          def->sel("self")->sel("reset"),
          def->sel("self")->sel("config_addr"),
          def->sel("self")->sel("config_data"),
          });

  cout << "Size of subcircuit = " << subCircuitInstances.size() << endl;
  // for (auto inst : subCircuitInstances) {
  //   cout << "\t" << inst->toString() << endl;
  // }

  deleteContext(c);
  
}

void testNodeAfterConstant() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 16;

  Type* clType = c->Record({
        {"in", c->BitIn()->Arr(width)},
          {"out0", c->Bit()->Arr(width)},
              {"out1", c->Bit()->Arr(width)}
    });

  Module* cl = g->newModuleDecl("cl", clType);
  ModuleDef* def = cl->newModuleDef();

  def->addInstance("neg_node", "coreir.neg", {{"width", Const::make(c, width)}});
  def->addInstance("const_node",
                   "coreir.const",
                   {{"width", Const::make(c, width)}},
                   {{"value", Const::make(c, BitVector(width, 12))}});

  def->connect("self.in", "neg_node.in");
  def->connect("neg_node.out", "self.out0");
  def->connect("const_node.out", "self.out1");

  cl->setDef(def);

  c->runPasses({"rungenerators"});

  auto subCircuitInstances =
    extractSubcircuit(cl, {def->sel("self")->sel("in")});

  cout << "Size of subciruit = " << subCircuitInstances.size() << endl;
  for (auto inst : subCircuitInstances) {
    cout << "\t" << inst->toString() << endl;
  }

  assert(subCircuitInstances.size() == 2);

  deleteContext(c);

}

int main() {
  testBasicSubCircuit();
  testNodeAfterConstant();
  testCGRAConfigSubcircuit();
}
