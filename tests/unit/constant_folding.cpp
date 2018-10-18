#include "coreir.h"

#include "coreir/libs/rtlil.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"
#include "coreir/passes/transform/packconnections.h"

using namespace std;
using namespace CoreIR;

void testFoldEquals() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  uint width = 2;
  uint cwidth = 32;

  Type* eqModTP = c->Record({{"out", c->Bit()}});

  Module* eqMod = g->newModuleDecl("eqMod", eqModTP);
  ModuleDef* def = eqMod->newModuleDef();

  def->addInstance("cmp", "coreir.eq", {{"width", Const::make(c, width)}});

  def->addInstance("c0", "coreir.const", {{"width", Const::make(c, cwidth)}}, {{"value", Const::make(c, BitVec(cwidth, 0x00000C00))}});

  def->addInstance("c1", "coreir.const", {{"width", Const::make(c, width)}}, {{"value", Const::make(c, BitVec(width, 3))}});

  def->connect("c0.out.10", "cmp.in0.0");
  def->connect("c0.out.11", "cmp.in0.1");

  def->connect("c1.out.0", "cmp.in1.0");
  def->connect("c1.out.1", "cmp.in1.1");

  def->connect("cmp.out", "self.out");

  c->runPasses({"rungenerators"});
  
  eqMod->setDef(def);
  if (!saveToFile(g, "_eqmod.json",eqMod)) {
    c->die();
  }

  SimulatorState originalState(eqMod);
  originalState.execute();
  assert(originalState.getBitVec("self.out") == BitVec(1, 1));
  
  foldConstants(eqMod);
  eqMod->print();
  deleteDeadInstances(eqMod);

  cout << "eqMod after folding constants" << endl;
  eqMod->print();

  assert(eqMod->getDef()->getInstances().size() == 1);

  SimulatorState state(eqMod);
  state.execute();
  assert(state.getBitVec("self.out") == BitVec(1, 1));

  deleteContext(c);
}

void testFoldRegister() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"clk", c->Named("coreir.clkIn")},
          {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("reg", "coreir.reg",
                   {{"width", Const::make(c, 3)}},
                   {{"init", Const::make(c, BitVec(3, 2))}});

  def->connect("reg.out", "reg.in");
  def->connect("self.clk", "reg.clk");
  def->connect("reg.out", "self.out");

  md->setDef(def);

  c->runPasses({"rungenerators", "fold-constants"});

  cout << "After folding constants" << endl;

  md->print();
  assert(def->getInstances().size() == 1);

  bool containsConst = false;
  for (auto instR : def->getInstances()) {
    Instance* inst = instR.second;
    if (getQualifiedOpName(*inst) == "coreir.const") {
      containsConst = true;
      break;
    }
  }

  assert(containsConst);

  SimulatorState state(md);
  state.setClock("self.clk", 0, 1);
  state.setValue("self.in", BitVec(3, 0));

  state.execute();

  assert(state.getBitVec("self.out") == BitVec(3, 2));

  deleteContext(c);

}

void testFoldRegArst() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"clk", c->Named("coreir.clkIn")},
          {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();


  def->addInstance("rstVal", "corebit.const", {{"value", Const::make(c, true)}});

  def->addInstance("wrapRst",
                   "coreir.wrap",
                   {{"type", Const::make(c, c->Named("coreir.arst"))}});

  def->addInstance("reg", "coreir.reg_arst",
                   {{"width", Const::make(c, 3)}},
                   {{"init", Const::make(c, BitVec(3, 2))}});

  def->connect("reg.out", "reg.in");
  def->connect("rstVal.out", "wrapRst.in");
  def->connect("wrapRst.out", "reg.arst");
  def->connect("self.clk", "reg.clk");
  def->connect("reg.out", "self.out");

  md->setDef(def);

  c->runPasses({"rungenerators", "fold-constants", "deletedeadinstances"});

  cout << "After folding constants" << endl;

  md->print();
  assert(def->getInstances().size() == 1);

  bool containsConst = false;
  for (auto instR : def->getInstances()) {
    Instance* inst = instR.second;
    if (getQualifiedOpName(*inst) == "coreir.const") {
      containsConst = true;
      break;
    }
  }

  assert(containsConst);

  SimulatorState state(md);
  state.setClock("self.clk", 0, 1);
  state.setValue("self.in", BitVec(3, 0));

  state.execute();

  assert(state.getBitVec("self.out") == BitVec(3, 2));

  deleteContext(c);

}

int main() {
  testFoldEquals();
  testFoldRegister();
  testFoldRegArst();
}
