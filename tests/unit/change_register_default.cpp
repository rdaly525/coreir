#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"clk", c->Named("coreir.clkIn")},
          {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("reg", "coreir.reg",
                   {{"width", Const::make(c, 3)}},
                   {{"init", Const::make(c, BitVec(3, 0))}});

  def->connect("self.in", "reg.in");
  def->connect("self.clk", "reg.clk");
  def->connect("reg.out", "self.out");

  md->setDef(def);

  cout << "Before changing register" << endl;
  md->print();

  Instance* r = def->getInstances().at("reg");
  cout << "reg init = " << r->getModArgs().at("init")->get<BitVector>() << endl;

  setRegisterInit("reg", BitVec(3, 1), md);

  r = def->getInstances().at("reg");
  cout << "reg init after = " << r->getModArgs().at("init")->get<BitVector>() << endl;;
  
  cout << "After changing register" << endl;
  md->print();

  SimulatorState state(md);
  state.setClock("self.clk", 0, 0);
  state.setValue("self.in", BitVec(3, 1));

  state.execute();

  assert(state.getRegister("reg") == BitVec(3, 1));

  c->runPasses({"rungenerators"});

  setRegisterInit("reg", BitVec(3, 3), md);

  SimulatorState state2(md);
  state2.setClock("self.clk", 0, 0);
  state2.setValue("self.in", BitVec(3, 1));

  state2.execute();

  assert(state2.getRegister("reg") == BitVec(3, 3));
  

  //assert(false);
  deleteContext(c);
}
