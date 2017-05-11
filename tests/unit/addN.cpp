#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.hpp"


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
    [](Context* c, Args args) { //Function to compute type
      uint width = args.at("width")->get<ArgInt>();
      uint N = args.at("N")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(N)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );


  Generator* addN = g->newGeneratorDecl("addN",g->getTypeGen("addN_type"),{{"width",AINT},{"N",AINT}});
  
  addN->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    assert((N & (N-1)) == 0); //Check if power of 2
    assert(N!=1);

    Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);
    Generator* add2 = stdlib->getGenerator("add2");
    Generator* addN = c->getGlobal()->getGenerator("addN");
    
    Arg* aWidth = c->argInt(width);
    
    def->addInstance("inst",add2,{{"width",aWidth}});
    def->wire("inst.out","self.out");
    
    if (N == 2) {
      def->wire("self.in.0","inst.in0");
      def->wire("self.in.1","inst.in1");
    }
    else {
      //Connect half instances
      Arg* aN2 = c->argInt(N/2);
      def->addInstance("addN_0",addN,{{"width",aWidth},{"N",aN2}});
      def->addInstance("addN_1",addN,{{"width",aWidth},{"N",aN2}});
      for (uint i=0; i<N/2; ++i) {
        def->wire({"self","in",to_string(i)},{"addN_0","in",to_string(i)});
        def->wire({"self","in",to_string(i+N/2)},{"addN_1","in",to_string(i)});
      }
      def->wire("addN_0.out","inst.in0");
      def->wire("addN_1.out","inst.in1");
    }
  });
  
  // Define Add12 Module
  Type* add12Type = c->Record({
    {"in8",c->BitIn()->Arr(13)->Arr(8)},
    {"in4",c->BitIn()->Arr(13)->Arr(4)},
    {"out",c->Bit()->Arr(13)}
  });

  Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);
  Module* add12 = g->newModuleDecl("Add12",add12Type);
  ModuleDef* def = add12->newModuleDef();
    def->addInstance("add8_upper",addN,{{"width",c->argInt(13)},{"N",c->argInt(8)}});
    def->addInstance("add4_lower",addN,{{"width",c->argInt(13)},{"N",c->argInt(4)}});
    def->addInstance("add2_join",stdlib->getGenerator("add2"),{{"width",c->argInt(13)}});
    def->wire("self.in8","add8_upper.in");
    def->wire("self.in4","add4_lower.in");
    def->wire("add8_upper.out","add2_join.in0");
    def->wire("add4_lower.out","add2_join.in1");
    def->wire("add2_join.out","self.out");
  add12->setDef(def);
  add12->print();
  
  bool err = false;
  cout << "Checking saving and loading pregen" << endl;
  saveModule(add12, "_add12.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  loadModule(c,"_add12.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  
  cout << "Running Generators" << endl;
  rungenerators(c,add12,&err);
  if (err) c->die();
  add12->print();
  
  cout << "Checking saving and loading postgen" << endl;
  saveModule(add12, "_add12Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  Module* m = loadModule(c,"_add12Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();

  deleteContext(c);
}
