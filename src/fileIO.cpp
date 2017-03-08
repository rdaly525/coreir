
#include "passes.hpp"
#include "stdlib.hpp"
#include "stdlib_v1.hpp"

Module* loadModule(Context* c, string filename) {
  uint n = 32;
  cout << "Loading from file: " << filename << endl;
  
  Namespace* stdlib = getStdlib(c);
  c->registerLib(stdlib);

  //Declare add2 Generator
  Generator* add2 = stdlib->getGenerator("add2");
  assert(add2);
  // Define Add4 Module
  Type* add4Type = c->Record({
      {"in",c->Array(4,c->Array(n,c->BitIn()))},
      {"out",c->Array(n,c->BitOut())}
  });
  Module* add4_n = c->newModuleDecl("Add4",add4Type);
  ModuleDef* def = add4_n->newModuleDef();
    Wireable* iface = def->getInterface();
    Wireable* add_00 = def->addInstanceGenerator("add00",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_01 = def->addInstanceGenerator("add01",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_1 = def->addInstanceGenerator("add1",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    
    def->wire(iface->sel("in")->sel(0),add_00->sel("in0"));
    //def->wire(iface->sel("in")->sel(1)->sel(3),add_00->sel("in0")->sel(3));
    def->wire(iface->sel("in")->sel(1),add_00->sel("in1"));
    def->wire(iface->sel("in")->sel(2),add_01->sel("in0"));
    def->wire(iface->sel("in")->sel(3),add_01->sel("in1"));

    def->wire(add_00->sel("out"),add_1->sel("in0"));
    def->wire(add_01->sel("out"),add_1->sel("in1"));

    def->wire(add_1->sel("out"),iface->sel("out"));
  add4_n->addDef(def);
  c->checkerrors();
  
  // Link v1 of library
  cout << "Linking stdlib!" << endl;
  Namespace* stdlib_v1 = getStdlib_v1(c);
  c->linkLib(stdlib_v1, stdlib);
 
  cout << "Checkign Errors 2" << endl;
  c->checkerrors();
  
  rungenerators(c,add4_n);
  
  add4_n->print();
  
  return add4_n;
}
