#include "coreir.h"

using namespace CoreIR;
using namespace std;

void saveRegModule() {
  Context* c = newContext();
  uint width = 32;

  Type* regType = c->Record({
      {"clk", c->Named("coreir.clkIn")},
        {"in", c->BitIn()->Arr(width)},
          {"out", c->Bit()->Arr(width)},
    });

  Module* regComb =
    c->getGlobal()->newModuleDecl("regComb", regType);

  ModuleDef* def = regComb->newModuleDef();

  def->addInstance("reg0", "coreir.reg", {{"width", Const::make(c, width)}}, {{"init", Const::make(c, BitVec(width, 24))}});


  def->connect("self.clk", "reg0.clk");  
  def->connect("self.in", "reg0.in");

  def->connect("reg0.out", "self.out");

  regComb->setDef(def);


  c->runPasses({"rungenerators"});
  
  SimulatorState state(regComb);
  state.setClock("self.clk", 0, 0);
  state.setValue("self.in", BitVec(width, 3));
  state.execute();

  cout << "self.out = " << state.getBitVec("self.out") << endl;
  cout << "correct  = " << BitVec(width, 24) << endl;

  assert(state.getBitVec("self.out") == BitVec(width, 24));

  cout << "Saving" << endl;

  if (!saveToFile(c->getGlobal(), "_register_with_init.json", regComb)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  deleteContext(c);
}

void loadRegModule() {
  uint width = 32;

  Context* c = newContext();

  Module* mod = nullptr;

  cout << "loading" << endl;
  if (!loadFromFile(c, "_register_with_init.json", &mod)) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }

  assert(mod != nullptr);
  assert(mod->hasDef());

  c->runPasses({"rungenerators"});
  
  SimulatorState state(mod);

  state.setClock("self.clk", 0, 0);
  state.setValue("self.in", BitVec(width, 3));
  state.execute();

  assert(state.getBitVec("self.out") == BitVec(width, 24));
  
  deleteContext(c);
}

int main() {
  saveRegModule();
  loadRegModule();

  assert(false);
}
