#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-passes/common.h"
#include "coreir-passes/firrtl.hpp"

using namespace CoreIR;

int main() {
  uint n = 32;
  
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  
  Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);
  
  //Declare add2 Generator
  Generator* add2 = stdlib->getGenerator("add");
  assert(add2);
  

  // Define Add4 Module
  Type* add4Type = c->Record({
      {"in",c->Array(4,c->Array(n,c->BitIn()))},
      {"out",c->Array(n,c->Bit())}
  });

  Module* add4_n = g->newModuleDecl("Add4",add4Type);
  ModuleDef* def = add4_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* add_00 = def->addInstance("add00",add2,{{"width",c->argInt(n)}});
    Wireable* add_01 = def->addInstance("add01",add2,{{"width",c->argInt(n)}});
    Wireable* add_1 = def->addInstance("add1",add2,{{"width",c->argInt(n)}});
    
    def->connect(self->sel("in")->sel(0),add_00->sel("in")->sel(0));
    def->connect(self->sel("in")->sel(1),add_00->sel("in")->sel(1));
    def->connect(self->sel("in")->sel(2),add_01->sel("in")->sel(0));
    def->connect(self->sel("in")->sel(3),add_01->sel("in")->sel(1));
    
    //def->connect(self->sel("in")->sel(3),add_01->sel("in1"));
    //def->connect(add_01->sel("in1"),self->sel("in")->sel(3));

    def->connect(add_00->sel("out"),add_1->sel("in")->sel(0));
    def->connect(add_01->sel("out"),add_1->sel("in")->sel(1));

    def->connect(add_1->sel("out"),self->sel("out"));
  add4_n->setDef(def);
  add4_n->print();
  
  bool err = false;
  cout << "Checking saving and loading pregen" << endl;
  saveModule(add4_n, "_add4.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  Module* m = loadModule(c,"_add4.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();
  
  
  PassManager* pm = new PassManager(g);
  pm->addPass(new PrintPass(),2);
  pm->addPass(new Firrtl(),5);
  pm->addPass(new Firrtl(),6);
  pm->run();
  // Link v1 of library
  //cout << "Linking stdlib!" << endl;
  //Namespace* stdlib_v1 = getStdlib_v1(c);
  //cout << "Linking!";
  //c->linkLib(stdlib_v1, stdlib);
  
  //rungenerators(c,add4_n,&err);
  //if (err) c->die();
  //add4_n->print();
  
  cout << "Checking saving and loading postgen" << endl;
  saveModule(add4_n, "_add4Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  m = loadModule(c,"_add4Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();

  deleteContext(c);
  
  return 0;
}
