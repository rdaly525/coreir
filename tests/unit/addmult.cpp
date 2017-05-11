#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.hpp"

using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);
  
  //Declare a brand new generator for some reason
 
  int constC = 3;

  //Type of module 
  Type* addmultType = c->Record({
    {"in",c->Array(16,c->BitIn())},
    {"out",c->Array(16,c->Bit())}
  });
 
  //These will eventually be generators where you can pass in '16'
  Module* add2_16 = stdlib->getModule("add2_16");
  Module* mult2_16 = stdlib->getModule("mult2_16");
  Module* const_16 = stdlib->getModule("const_16");
  Module* addmult = c->getGlobal()->newModuleDecl("addmult",addmultType);
  ModuleDef* def = addmult->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* addinst = def->addInstance("addinst",add2_16);
    Wireable* multinst = def->addInstance("multinst",mult2_16);
    Wireable* constinst = def->addInstance("const3",const_16,{{"value",c->argInt(constC)}});
    def->wire(self->sel("in"),addinst->sel("in0"));
    def->wire(constinst->sel("out"),addinst->sel("in1"));
    def->wire(constinst->sel("out"),multinst->sel("in0"));
    def->wire(addinst->sel("out"),multinst->sel("in1"));

  addmult->setDef(def);

  addmult->print();
  
  bool err = false;
  //Save to Json
  cout << "Saving 2 json" << endl;
  saveModule(addmult,"_addmult.json",&err);
  if(err) c->die();
  deleteContext(c);

  c = newContext();
  CoreIRLoadLibrary_stdlib(c); 
  cout << "Loading json" << endl;
  Module* m = loadModule(c,"_addmult.json",&err);
  if(err) c->die();
  cout << "Saving json again" << endl;
  saveModule(m,"_addmult2.json",&err);
  c->getGlobal()->print();
  deleteContext(c);
  return 0;
}
