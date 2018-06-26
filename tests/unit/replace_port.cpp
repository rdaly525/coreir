#include "coreir.h"

using namespace CoreIR;
using namespace std;

void testReplaceArrayPort() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("neg", "coreir.not", {{"width", Const::make(c, 3)}});
  def->connect("self.in", "neg.in");
  def->connect("neg.out", "self.out");

  md->setDef(def);

  portToConstant("in", BitVec(3, 5), md);

  cout << "module after" << endl;
  md->print();

  SimulatorState state(md);
  state.execute();

  cout << "self.out      = " << state.getBitVec("self.out") << endl;
  cout << "~BitVec(3, 5) = " << ~BitVec(3, 5) << endl;

  assert(state.getBitVec("self.out") == ~BitVec(3, 5));

  deleteContext(c);

}

void testReplaceBitPort() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()},
        {"out", c->Bit()}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("neg", "corebit.not");
  def->connect("self.in", "neg.in");
  def->connect("neg.out", "self.out");

  md->setDef(def);

  portToConstant("in", BitVec(1, 0), md);

  bool error = md->getDef()->validate();
  assert(!error);

  if (!saveToFile(c->getGlobal(), "_bit_replacement.json", md)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  cout << "module after" << endl;
  md->print();

  SimulatorState state(md);
  state.execute();

  cout << "self.out      = " << state.getBitVec("self.out") << endl;

  assert(state.getBitVec("self.out") == ~BitVec(1, 0));

  deleteContext(c);
}

void testBuildBitArrayToBit() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()},
        {"out", c->Bit()}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("def_self_const_replace_0",
                   "coreir.const",
                   {{"width", Const::make(c, 1)}},
                   {{"value", Const::make(c, BitVec(1, 0))}});

  def->addInstance("neg", "corebit.not");
  def->connect("def_self_const_replace_0.out", "neg.in");
  def->connect("neg.out", "self.out");

  cout << "Manually created def" << endl;
  def->print();
  bool is_error = def->validate();
  assert(!is_error);

  md->setDef(def);

  // portToConstant("in", BitVec(1, 0), md);

  // if (!saveToFile(c->getGlobal(), "bit_replacement.json", md)) {
  //   cout << "Could not save to json!!" << endl;
  //   c->die();
  // }
  
  // cout << "module after" << endl;
  // md->print();

  // SimulatorState state(md);
  // state.execute();

  // cout << "self.out      = " << state.getBitVec("self.out") << endl;

  // assert(state.getBitVec("self.out") == ~BitVec(1, 0));

  deleteContext(c);

  assert(false);
}

int main() {
  testReplaceArrayPort();
  testReplaceBitPort();
  //testBuildBitArrayToBit();
}
