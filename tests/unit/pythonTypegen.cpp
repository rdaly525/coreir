#include "coreir.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Put this addN in the global namespace
  Namespace* g = c->getGlobal();
  
  //Declare a TypeGenerator (in global) for addN
  g->newTypeGen(
    "addN_type", //name for the typegen
    {{"width",AINT},{"N",AINT}}, //generater parameters
    "add",
    "type_gen"
  );
  exit(1);


  // Generator* addN = g->newGeneratorDecl("addN",g->getTypeGen("addN_type"),{{"width",AINT},{"N",AINT}});
  // 
  // addN->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
  //   uint width = args.at("width")->get<int>();
  //   uint N = args.at("N")->get<int>();
  //   assert((N & (N-1)) == 0); //Check if power of 2
  //   assert(N!=1);

  //   Namespace* coreir = c->getNamespace("coreir");
  //   Generator* add2 = coreir->getGenerator("add");
  //   Generator* addN = c->getGlobal()->getGenerator("addN");
  //   
  //   ArgPtr aWidth = Const(width);
  //   
  //   def->addInstance("join",add2,{{"width",aWidth}});
  //   def->connect("join.out","self.out");
  //   
  //   if (N == 2) {
  //     def->connect("self.in.0","join.in0");
  //     def->connect("self.in.1","join.in1");
  //   }
  //   else {
  //     //Connect half instances
  //     ArgPtr aN2 = Const(N/2);
  //     def->addInstance("addN_0",addN,{{"width",aWidth},{"N",aN2}});
  //     def->addInstance("addN_1",addN,{{"width",aWidth},{"N",aN2}});
  //     for (uint i=0; i<N/2; ++i) {
  //       def->connect({"self","in",to_string(i)},{"addN_0","in",to_string(i)});
  //       def->connect({"self","in",to_string(i+N/2)},{"addN_1","in",to_string(i)});
  //     }
  //     def->connect("addN_0.out","join.in0");
  //     def->connect("addN_1.out","join.in1");
  //   }
  // });
  // 
  // // Define Add12 Module
  // Type* add12Type = c->Record({
  //   {"in8",c->BitIn()->Arr(13)->Arr(8)},
  //   {"in4",c->BitIn()->Arr(13)->Arr(4)},
  //   {"out",c->Bit()->Arr(13)}
  // });

  // Namespace* coreir = c->getNamespace("coreir");
  // Module* add12 = g->newModuleDecl("Add12",add12Type);
  // ModuleDef* def = add12->newModuleDef();
  //   def->addInstance("add8_upper",addN,{{"width",Const(13)},{"N",Const(8)}});
  //   def->addInstance("add4_lower",addN,{{"width",Const(13)},{"N",Const(4)}});
  //   def->addInstance("add2_join",coreir->getGenerator("add"),{{"width",Const(13)}});
  //   def->connect("self.in8","add8_upper.in");
  //   def->connect("self.in4","add4_lower.in");
  //   def->connect("add8_upper.out","add2_join.in0");
  //   def->connect("add4_lower.out","add2_join.in1");
  //   def->connect("add2_join.out","self.out");
  // add12->setDef(def);
  // add12->print();
  // 
  // c->runPasses({"rungenerators","flatten"});
  // add12->print();

  // deleteContext(c);
}
