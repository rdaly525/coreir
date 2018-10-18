#include "coreir.h"

using namespace CoreIR;

int main() {
  
  Context* c = newContext();
  
  Type* CounterType = c->Record({
    {"en",c->BitIn()},
    {"out",c->Array(16,c->Bit())},
    {"clk",c->Named("coreir.clkIn")},
  });
  
  Module* counter = c->getGlobal()->newModuleDecl("counter",CounterType);

  ModuleDef* counterDef = counter->newModuleDef();
    
    Values widthArg = {{"width",Const::make(c,16)}};
    counterDef->addInstance("ai","coreir.add",widthArg);
    counterDef->addInstance("ci","coreir.const",widthArg,{{"value",Const::make(c,16,1)}});
    counterDef->addInstance(
      "ri",
      "mantle.reg",
      {{"width",Const::make(c,16)},{"has_en",Const::make(c,true)}},
      {{"init",Const::make(c,16,0)}}
    );
    
    counterDef->connect("self.clk","ri.clk");
    counterDef->connect("self.en","ri.en");
    counterDef->connect("ci.out","ai.in0");
    counterDef->connect("ai.out","ri.in");
    counterDef->connect("ri.out","ai.in1");
    counterDef->connect("ri.out","self.out");

  counter->setDef(counterDef);

  counter->print();
  
  c->runPasses({"verifyconnectivity"});

  deleteContext(c);
  return 0;
}
