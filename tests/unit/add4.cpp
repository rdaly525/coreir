#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  uint n = 32;
  
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  
  Generator* add2 = c->getGenerator("coreir.add");

  // Define Add4 Module
  Type* add4Type = c->Record({
      {"in",c->Array(4,c->Array(n,c->BitIn()))},
      {"out",c->Array(n,c->Bit())}
  });

  Module* add4_n = g->newModuleDecl("Add4",add4Type);
  ModuleDef* def = add4_n->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* add_00 = def->addInstance("add00",add2,{{"width",Const::make(c,n)}});
    Wireable* add_01 = def->addInstance("add01",add2,{{"width",Const::make(c,n)}});
    Wireable* add_1 = def->addInstance("add1",add2,{{"width",Const::make(c,n)}});
    
    def->connect(self->sel("in")->sel(0),add_00->sel("in0"));
    def->connect(self->sel("in")->sel(1),add_00->sel("in1"));
    def->connect(self->sel("in")->sel(2),add_01->sel("in0"));
    def->connect(self->sel("in")->sel(3),add_01->sel("in1"));

    def->connect(add_00->sel("out"),add_1->sel("in0"));
    def->connect(add_01->sel("out"),add_1->sel("in1"));

    def->connect(add_1->sel("out"),self->sel("out"));
  add4_n->setDef(def);
  add4_n->print();

  deleteContext(c);
  
  return 0;
}
