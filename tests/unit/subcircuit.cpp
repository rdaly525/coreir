#include "coreir.h"

#include "coreir/libs/rtlil.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"
#include "coreir/passes/transform/packconnections.h"

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

  def->addInstance("config_reg", "corebit.reg");
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

// void testCGRAConfigSubcircuit() {
//   Context* c = newContext();

//   Module* topMod = nullptr;

//   cout << "Loading CGRA" << endl;

// Q: How did this ever pass on travis??
//   if (!loadFromFile(c,"/Users/dillon/VerilogWorkspace/CGRAGenerator/hardware/generator_z/top/top_flat_clk.json", &topMod)) {
//     cout << "Could not Load from json!!" << endl;
//     c->die();
//   }

//   cout << "Loaded CGRA" << endl;

//   assert(topMod != nullptr);

//   assert(topMod->hasDef());

//   ModuleDef* def = topMod->getDef();

//   vector<Wireable*> subCircuitPorts{def->sel("self")->sel("clk"),
//           def->sel("self")->sel("reset"),
//           def->sel("self")->sel("config_addr"),
//           def->sel("self")->sel("config_data"),
//       };

//   auto subCircuitInstances =
//     extractSubcircuit(topMod, subCircuitPorts);

//   cout << "Size of subcircuit = " << subCircuitInstances.size() << endl;
//   int i = 0;
//   for (auto inst : subCircuitInstances) {
//     if ((getQualifiedOpName(*inst) == "coreir.reg") ||
//         (getQualifiedOpName(*inst) == "coreir.regrst") ||
//         (getQualifiedOpName(*inst) == "corebit.reg")) {
//       i++;
//       //cout << "\t" << inst->toString() << " : " << inst->getModuleRef()->toString() << endl;
//     }
//   }

//   cout << "# of registers = " << i << endl;

//   addSubcircuitModule("top_config",
//                       topMod,
//                       subCircuitPorts,
//                       subCircuitInstances,
//                       c,
//                       c->getGlobal());


//   Module* topConfig = c->getGlobal()->getModule("top_config");
//   cout << "Deleting dead instances" << endl;
//   deleteDeadInstances(topConfig);
//   cout << "Done deleting dead instances" << endl;

//   cout << "# of top config instances " << topConfig->getDef()->getInstances().size() << endl;
//   cout << "# of top config connections " << topConfig->getDef()->getConnections().size() << endl;

//   deleteContext(c);
  
// }

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

  // Extract the configuration subcircuit
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
  assert(miniChip_conf->hasDef());

  ModuleDef* mcDef = miniChip_conf->getDef();
  cout << "miniChip config instances" << endl;
  for (auto instR : mcDef->getInstances()) {
    cout << "\t" << instR.second->toString() << endl;
  }

  cout << "miniChip config connections" << endl;
  for (auto conn : mcDef->getConnections()) {
    cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
  }

  SimulatorState state(miniChip_conf);
  state.setValue("self.config_addr", BitVec(addr_width, 12));
  state.setValue("self.config_data", BitVec(1, 1));
  state.setClock("self.clk", 0, 1);

  state.execute();
  state.execute();

  assert(state.getBitVec("self.config_data_reg$reg0_subcircuit_out") ==
         BitVec(1, 1));

  registersToConstants(miniChip, state.getCircStates().back().registers);
  deleteDeadInstances(miniChip);
  //unpackConnections(miniChip);
  foldConstants(miniChip);
  deleteDeadInstances(miniChip);

  c->runPasses({"packconnections"});

  cout << "miniChip partially evaluated instances" << endl;
  for (auto instR : miniChip->getDef()->getInstances()) {
    cout << "\t" << instR.second->toString() << endl;
  }

  cout << "miniChip partially evaluated connections" << endl;
  for (auto conn : miniChip->getDef()->getConnections()) {
    cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
  }

  assert(miniChip->getDef()->getInstances().size() == 2);

  SimulatorState fs(miniChip);
  fs.setValue("self.in0", BitVec(width, 234));
  fs.setValue("self.in1", BitVec(width, 34534));
  fs.setClock("self.clk", 0, 1);

  fs.execute();
  fs.execute();

  assert(fs.getBitVec("self.out") == BitVec(width, 234 | 34534));
  
  deleteContext(c);
}

void testCGRAConnectBox() {
  Context* c = newContext();

  Module* topMod = nullptr;

  if (!loadFromFile(c, "cb_unq_proc_sanitized_names.json", &topMod)) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }

  c->runPasses({"removeconstduplicates"});
  assert(topMod->hasDef());

  ModuleDef* def = topMod->getDef();

  // Extract the configuration subcircuit
  vector<Wireable*> subCircuitPorts{def->sel("self")->sel("config_addr"),
      def->sel("self")->sel("config_data"),
      def->sel("self")->sel("config_en"),
      def->sel("self")->sel("clk"),
      def->sel("self")->sel("reset")};

  auto subCircuitInstances =
    extractSubcircuit(topMod, subCircuitPorts);

  cout << "Size of subciruit = " << subCircuitInstances.size() << endl;
  for (auto inst : subCircuitInstances) {
    cout << "\t" << inst->toString() << endl;
  }

  // Create the subcircuit for the config
  addSubcircuitModule("topMod_config",
                      topMod,
                      subCircuitPorts,
                      subCircuitInstances,
                      c,
                      c->getGlobal());

  Module* topMod_conf =
    c->getGlobal()->getModule("topMod_config");

  // cout << "topMod_config interface" << endl;
  // cout << topMod_conf->toString() << endl;

  assert(topMod_conf != nullptr);
  assert(topMod_conf->hasDef());

  // ModuleDef* mcDef = topMod_conf->getDef();
  // cout << "topMod config instances" << endl;
  // for (auto instR : mcDef->getInstances()) {
  //   cout << "\t" << instR.second->toString() << endl;
  // }

  // cout << "topMod config connections" << endl;
  // for (auto conn : mcDef->getConnections()) {
  //   cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
  // }

  c->runPasses({"clockifyinterface"});

  SimulatorState configState(topMod_conf);
  configState.setClock("self.clk", 0, 1);
  configState.setValue("self.config_en", BitVec(1, 1));
  configState.setValue("self.config_addr", BitVec(32, 0));
  configState.setValue("self.config_data", BitVec(32, 6));
  configState.setValue("self.reset", BitVec(1, 0));

  configState.execute();
  configState.execute();

  //assert(configState.getBitVec("__DOLLAR__procdff__DOLLAR__26UDOLLARUreg0.out") == BitVec(32, 6));

  cout << "# of instances in topMod before partial eval = " << topMod->getDef()->getInstances().size() << endl;

  auto regs = configState.getCircStates().back().registers;
  cout << "Connect box converting " << regs.size() << " registers to constants" << endl;
  for (auto reg : regs) {
    cout << "\t" << reg.first << " ---> " << reg.second << endl;
  }

  registersToConstants(topMod, regs);

  // if (!saveToFile(c->getGlobal(), "registered_connect_box.json", topMod)) {
  //   cout << "Could not save to json!!" << endl;
  //   c->die();
  // }
  
  // cout << "connect box partially evaluated:" << endl;
  // topMod->print();

  deleteDeadInstances(topMod);
  //unpackConnections(topMod);
  foldConstants(topMod);
  deleteDeadInstances(topMod);

  c->runPasses({"packconnections"});

  cout << "# of instances in topMod after partial eval = " << topMod->getDef()->getInstances().size() << endl;

  assert(topMod->getDef()->getInstances().size() == 0);

  cout << "topMod partially evaluated instances" << endl;
  for (auto instR : topMod->getDef()->getInstances()) {
    cout << "\t" << instR.second->toString() << " : " << instR.second->getModuleRef()->toString() << endl;
  }

  cout << "topMod partially evaluated connections" << endl;
  for (auto conn : topMod->getDef()->getConnections()) {
    cout << "\t" << conn.first->toString() << " <-> " <<
      conn.second->toString() << endl;
  }

  // assert(topMod->getDef()->getInstances().size() == 2);

  c->runPasses({"clockifyinterface"});
  
  SimulatorState fs(topMod);
  fs.setValue("self.in_0", BitVec(16, 0));
  fs.setValue("self.in_1", BitVec(16, 1));
  fs.setValue("self.in_2", BitVec(16, 2));
  fs.setValue("self.in_3", BitVec(16, 3));
  fs.setValue("self.in_4", BitVec(16, 4));
  fs.setValue("self.in_5", BitVec(16, 5));
  fs.setValue("self.in_6", BitVec(16, 6));
  fs.setValue("self.in_7", BitVec(16, 7));
  fs.setValue("self.in_8", BitVec(16, 8));
  fs.setValue("self.in_9", BitVec(16, 9));
  //fs.setClock("self.clk", 0, 1);

  fs.execute();
  fs.execute();

  assert(fs.getBitVec("self.out") == BitVec(16, 6));

  deleteContext(c);

}

void testCGRASwitchBox() {

  Context* c = newContext();

  Module* topMod = nullptr;

  if (!loadFromFile(c, "sb_unq4_proc_sanitized_names.json", &topMod)) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }

  c->runPasses({"removeconstduplicates"});

  assert(topMod->hasDef());

  ModuleDef* def = topMod->getDef();

  // Extract the configuration subcircuit
  vector<Wireable*> subCircuitPorts{def->sel("self")->sel("config_addr"),
      def->sel("self")->sel("config_data"),
      def->sel("self")->sel("config_en"),
      def->sel("self")->sel("clk"),
      def->sel("self")->sel("reset")};

  auto subCircuitInstances =
    extractSubcircuit(topMod, subCircuitPorts);

  // cout << "Size of subciruit = " << subCircuitInstances.size() << endl;
  // for (auto inst : subCircuitInstances) {
  //   cout << "\t" << inst->toString() << endl;
  // }

  // Create the subcircuit for the config
  addSubcircuitModule("topMod_config",
                      topMod,
                      subCircuitPorts,
                      subCircuitInstances,
                      c,
                      c->getGlobal());

  Module* topMod_conf =
    c->getGlobal()->getModule("topMod_config");

  // cout << "topMod_config interface" << endl;
  // cout << topMod_conf->toString() << endl;

  assert(topMod_conf != nullptr);
  assert(topMod_conf->hasDef());

  // ModuleDef* mcDef = topMod_conf->getDef();
  // cout << "topMod config instances" << endl;
  // for (auto instR : mcDef->getInstances()) {
  //   cout << "\t" << instR.second->toString() << endl;
  // }

  // cout << "topMod config connections" << endl;
  // for (auto conn : mcDef->getConnections()) {
  //   cout << "\t" << conn.first->toString() << " <-> " << conn.second->toString() << endl;
  // }

  c->runPasses({"clockifyinterface"});
  
  SimulatorState configState(topMod_conf);
  configState.setClock("self.clk", 0, 1);
  configState.setValue("self.config_en", BitVec(1, 1));
  configState.setValue("self.config_addr", BitVec(32, 0));
  configState.setValue("self.config_data", BitVec(32, 6));
  configState.setValue("self.reset", BitVec(1, 0));

  configState.execute();
  configState.execute();

  // assert(configState.getBitVec("__DOLLAR__procdff__DOLLAR__26$reg0.out") == BitVec(32, 6));

  cout << "# of instances in topMod before partial eval = " << topMod->getDef()->getInstances().size() << endl;

  auto regs = configState.getCircStates().back().registers;
  cout << "Connect box converting " << regs.size() << " registers to constants" << endl;
  for (auto reg : regs) {
    cout << "\t" << reg.first << " ---> " << reg.second << endl;
  }
  
  registersToConstants(topMod, regs);

  deleteDeadInstances(topMod);
  foldConstants(topMod);
  deleteDeadInstances(topMod);

  c->runPasses({"packconnections"});

  cout << "# of instances in topMod after partial eval = " << topMod->getDef()->getInstances().size() << endl;

  assert(topMod->getDef()->getInstances().size() == 0);

  cout << "switch box partially evaluated connections" << endl;
  for (auto conn : topMod->getDef()->getConnections()) {
    cout << "\t" << conn.first->toString() << " <-> " <<
      conn.second->toString() << endl;
  }

  //assert(false);

  deleteContext(c);

}

void testMixedRegister() {

  Context* c = newContext();

  Type* tp = c->Record({
      {"config_data", c->BitIn()->Arr(8)},
        {"data", c->BitIn()->Arr(2)},
          {"const_val", c->BitIn()->Arr(2)}
    });

  Module* m = c->getGlobal()->newModuleDecl("opt_reg", tp);
  ModuleDef* def = m->newModuleDef();

  //def->addInstance("");

  m->setDef(def);
  
  deleteContext(c);

  //assert(false);
}

int main() {
  testMixedRegister();
  testBasicSubCircuit();
  testNodeAfterConstant();
  testSubcircuitModule();
  testCGRAConnectBox();
  testCGRASwitchBox();
}
