
#include "context.hpp"
#include "stdlib.hpp"
#include "passes.hpp"


using namespace CoreIR;


// Create the following circuit
//
//       in1
//           \
// in0 - Add - Mult - out
//     / 
//   C 

int main() {
  Context* c = newContext();

  Namespace* stdlib = getStdlib(c);
  
  int constC = 3;

  //Type of module 
  Type* addmultType = c->Record({
    {"in0",c->Array(16,c->BitIn())},
    {"in1",c->Array(16,c->BitIn())},
    {"out",c->Array(16,c->BitOut())}
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
    Wireable* constinst = def->addInstance("const3",const_16,c->newGenArgs({{"value",c->GInt(constC)}}));
    def->wire(self->sel("in0"),addinst->sel("in0"));
    def->wire(constinst,addinst->sel("in1"));
    def->wire(self->sel("in1"),multinst->sel("in0"));
    def->wire(addinst->sel("out"),multinst->sel("in2"));
  addmult->addDef(def);

  addmult->print();
  
  bool err = false;
 
  //Do typechecking
  typecheck(c,addmult,&err);
  if(err) c->die();

  //Save to Json
  saveModule(addmult,"addmult.json",&err);
  if(err) c->die();

  deleteContext(c);
  return 0;
}
