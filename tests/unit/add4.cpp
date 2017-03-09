#include "context.hpp"
//#include "toFile.hpp"

//#include <fstream>

// Libraries
#include "stdlib.hpp"
#include "stdlib_v1.hpp"

//Compiler Passes
#include "passes.hpp"


int main() {
  uint n = 32;
  
  // New context
  Context* c = newContext();
  Namespace* g = c->getGlobal();
  //register the stdlib
  Namespace* stdlib = getStdlib(c);

  stdlib->print();

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
  cout << "Checkign Errors 1" << endl;
  c->checkerrors();
  add4_n->print();

  //if (typecheck(c,add4_n)) c->die();
  //rungenerators(c,add4_n);
  //if (typecheck(c,add4_n)) c->die();
  
  // Link v1 of library
  cout << "Linking stdlib!" << endl;
  Namespace* stdlib_v1 = getStdlib_v1(c);
  cout << "Linking!";
  c->linkLib(stdlib_v1, stdlib);
 
  cout << "Checkign Errors 2" << endl;
  c->checkerrors();
  stdlib->print();
  
  rungenerators(c,add4_n);
  
  add4_n->print();
  cout << "Typechecking!" << endl;
  if (typecheck(c,add4_n)) c->die();
  if (saveModule(add4_n, "add4n.json")) {
    cout << "Failed" << endl;
  }


  //Add Def to global
  //c->getGlobal()->addModule(add4_n);
    
  // emit this circuit as a file
  //toFileMain(add4, "add4.core");

  //fstream f;
  //f.open("add4.v",fstream::out);
  //assert(f.is_open());
  //compile(c,add4,&f);
  //f.close();

  deleteContext(c);
  
  return 0;
}
