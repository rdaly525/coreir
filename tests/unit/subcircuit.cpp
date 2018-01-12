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

  vector<Wireable*> subCircuitPorts{def->sel("self")->sel("clk"),
          def->sel("self")->sel("reset"),
          def->sel("self")->sel("config_addr"),
          def->sel("self")->sel("config_data"),
      };

  auto subCircuitInstances =
    extractSubcircuit(topMod, subCircuitPorts);

  cout << "Size of subcircuit = " << subCircuitInstances.size() << endl;
  for (auto inst : subCircuitInstances) {
    if ((getQualifiedOpName(*inst) == "coreir.reg") ||
        (getQualifiedOpName(*inst) == "coreir.regrst") ||
        (getQualifiedOpName(*inst) == "corebit.dff")) {
      cout << "\t" << inst->toString() << " : " << inst->getModuleRef()->toString() << endl;
    }
  }

  addSubcircuitModule("top_config",
                      topMod,
                      subCircuitPorts,
                      subCircuitInstances,
                      c,
                      c->getGlobal());
  

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

void testSubcircuitModule() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 32;
  uint addr_width = 16;

  Type* miniChipType = c->Record({
      {"in0", c->BitIn()->Arr(width)},
        {"in1", c->BitIn()->Arr(width)},
          {"config_addr", c->BitIn()->Arr(addr_width)},
            {"config_data", c->BitIn()},
              {"clk", c->Named("coreir.clkIn")},
                {"out", c->Bit()->Arr(width)}
    });

  Module* miniChip = g->newModuleDecl("miniChip", miniChipType);
  ModuleDef* def = miniChip->newModuleDef();

  def->addInstance("config_data_reg",
                   "mantle.reg",
                   {{"width", Const::make(c, 1)},
                       {"has_en", Const::make(c, true)}});

  def->addInstance("compare_addr",
                   "coreir.eq",
                   {{"width", Const::make(c, addr_width)}});

  def->addInstance("and_op",
                   "coreir.and",
                   {{"width", Const::make(c, width)}});

  def->addInstance("or_op",
                   "coreir.or",
                   {{"width", Const::make(c, width)}});

  def->addInstance("op_select",
                   "coreir.mux",
                   {{"width", Const::make(c, width)}});

  def->addInstance("out_reg",
                   "coreir.reg",
                   {{"width", Const::make(c, width)}});

  def->addInstance("chip_addr",
                   "coreir.const",
                   {{"width", Const::make(c, addr_width)}},
                   {{"value", Const::make(c, BitVec(addr_width, 12))}});

  // Wire up clock
  def->connect("self.clk", "config_data_reg.clk");
  def->connect("self.clk", "out_reg.clk");

  // Wire up data inputs
  def->connect("self.in0", "and_op.in0");
  def->connect("self.in1", "and_op.in1");

  def->connect("self.in0", "or_op.in0");
  def->connect("self.in1", "or_op.in1");
  
  // Wire up data outputs
  def->connect("and_op.out", "op_select.in0");
  def->connect("or_op.out", "op_select.in1");
  def->connect("op_select.out", "out_reg.in");
  def->connect("out_reg.out", "self.out");

  // Wire up config select
  def->connect("self.config_addr", "compare_addr.in0");
  def->connect("chip_addr.out", "compare_addr.in1");
  def->connect("compare_addr.out", "config_data_reg.en");
  def->connect("self.config_data", "config_data_reg.in.0");
  def->connect("config_data_reg.out.0", "op_select.sel");

  miniChip->setDef(def);

  c->runPasses({"rungenerators", "flatten"});

  vector<Wireable*> subCircuitPorts{def->sel("self")->sel("config_addr"),
      def->sel("self")->sel("config_data"),
      def->sel("self")->sel("clk")};

  auto subCircuitInstances =
    extractSubcircuit(miniChip, subCircuitPorts);

  cout << "Size of subciruit = " << subCircuitInstances.size() << endl;
  for (auto inst : subCircuitInstances) {
    cout << "\t" << inst->toString() << endl;
  }

  assert(subCircuitInstances.size() == 4);

  // Create the subcircuit for the config
  addSubcircuitModule("miniChip_config",
                      miniChip,
                      subCircuitPorts,
                      subCircuitInstances,
                      c,
                      c->getGlobal());

  Module* miniChip_conf =
    c->getGlobal()->getModule("miniChip_config");

  assert(miniChip_conf != nullptr);

  deleteContext(c);
}

int main() {
  testBasicSubCircuit();
  testNodeAfterConstant();
  testSubcircuitModule();
  testCGRAConfigSubcircuit();
}
