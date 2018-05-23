#include "coreir.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  Context* c = newContext();
  Namespace* g = c->getGlobal();
  
  //Declare an implicit TypeGenerator
  TypeGen* tg = TypeGenImplicit::make(
    g,
    "add_type", //name for the typegen
    {{"width",c->Int()}} //generater parameters
  );

  Generator* add = g->newGeneratorDecl("add",tg,{{"width",c->Int()}});
  
  {
    Module* m5 = add->getModule(
      {{"width",Const::make(c,5)}},
      c->Record({
        {"in0",c->BitIn()->Arr(5)},
        {"in1",c->BitIn()->Arr(5)},
        {"out",c->Bit()->Arr(5)}
      })
    );

    ModuleDef* def = m5->newModuleDef();
    def->addInstance("i0","coreir.add",{{"width",Const::make(c,5)}});
    def->connect("self","i0");
  }

  {
    Module* m9 = add->getModule(
      {{"width",Const::make(c,9)}},
      c->Record({
        {"in0",c->BitIn()->Arr(9)},
        {"in1",c->BitIn()->Arr(9)},
        {"out",c->Bit()->Arr(9)}
      })
    );

    ModuleDef* def = m9->newModuleDef();
    def->addInstance("i0","coreir.add",{{"width",Const::make(c,9)}});
    def->connect("self","i0");
  }

  // Define Add12 Module
  Module* top = g->newModuleDecl("top",c->Record());
  ModuleDef* def = top->newModuleDef();
    def->addInstance("add5","global.add",{{"width",Const::make(c,5)}});
    def->addInstance("add9","global.add",{{"width",Const::make(c,9)}});
  top->setDef(def);
  top->print();
  
  cout << "Checking saving and loading postgen" << endl;
  if (!saveToFile(g, "_typegen_implicit.json",top)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  deleteContext(c);
  
  c = newContext();
  
  top = nullptr;
  if (!loadFromFile(c,"_typegen_implicit.json", &top)) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  ASSERT(top, "Could not load top: typegen_implicit");
  top->print();

  c->runPasses({"rungenerators","flatten"});
  top->print();

}
