#include "context.hpp"
//#include "toFile.hpp"

//#include <fstream>

// Libraries
#include "stdlib.hpp"

//Compiler Passes
#include "passes.hpp"


int main() {
  uint n = 32;
  
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  
  Namespace* stdlib = getStdlib(c);

  //Declare add2 Generator
  Generator* add2 = stdlib->getGenerator("add2");
  assert(add2);
  
  // Define Add4 Module
  Type* add4Type = c->Record({
      {"in",c->Array(4,c->Array(n,c->BitIn()))},
      {"out",c->Array(n,c->BitOut())}
  });

  Module* add4_n = g->newModuleDecl("Add4",add4Type);
  ModuleDef* def = add4_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* add_00 = def->addInstanceGenerator("add00",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_01 = def->addInstanceGenerator("add01",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_1 = def->addInstanceGenerator("add1",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    
    def->wire(self->sel("in")->sel(0),add_00->sel("in0"));
    //def->wire(self->sel("in")->sel(1)->sel(3),add_00->sel("in0")->sel(3));
    def->wire(self->sel("in")->sel(1),add_00->sel("in1"));
    def->wire(self->sel("in")->sel(2),add_01->sel("in0"));
    def->wire(self->sel("in")->sel(3),add_01->sel("in1"));

    def->wire(add_00->sel("out"),add_1->sel("in0"));
    def->wire(add_01->sel("out"),add_1->sel("in1"));

    def->wire(add_1->sel("out"),self->sel("out"));
  add4_n->addDef(def);
  cout << "Checkign Errors 1" << endl;
  c->checkerrors();
  add4_n->print();

  if (typecheck(c,add4_n)) c->die();
  
  // Link v1 of library
  //cout << "Linking stdlib!" << endl;
  //Namespace* stdlib_v1 = getStdlib_v1(c);
  //cout << "Linking!";
  //c->linkLib(stdlib_v1, stdlib);
 
  cout << "Checkign Errors 2" << endl;
  c->checkerrors();
  //stdlib->print();
  rungenerators(c,add4_n);
  add4_n->print();
  cout << "Typechecking!" << endl;
  if (typecheck(c,add4_n)) c->die();
 
  
  bool err = false;
  saveModule(add4_n, "_add4.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    deleteContext(c);
    return 1;
  }
  
  
  deleteContext(c);
  
  return 0;
}
