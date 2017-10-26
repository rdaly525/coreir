#include "coreir.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Put this add4 in the global namespace
  Namespace* g = c->getGlobal();
  
  //Declare a TypeGenerator (in global) for add4
  g->newTypeGen(
    "add4_type", //name for the typegen
    {{"width",c->Int()}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(4)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );


  Generator* add4 = g->newGeneratorDecl("add4",g->getTypeGen("add4_type"),{{"width",c->Int()}});
  
  add4->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint n = args.at("width")->get<int>();
    
    Namespace* coreir = c->getNamespace("coreir");
    auto add2 = coreir->getGenerator("add");
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
  });
 
  Type* t = g->getTypeGen("add4_type")->getType({{"width",Const::make(c,13)}});
  
  Module* add = g->newModuleDecl("Add",t);
  ModuleDef* def = add->newModuleDef();
    Instance* inst = def->addInstance("i0",add4,{{"width",Const::make(c,13)}});
    for (uint i=0; i<4; ++i) {
      def->connect(inst->sel("in")->sel(i),def->getInterface()->sel("in")->sel(i));
    }
    def->connect(inst->sel("out"),def->getInterface()->sel("out"));
    add4->runAll();
    inlineInstance(inst);
  add->setDef(def);
  add->print();
  deleteContext(c);

}
