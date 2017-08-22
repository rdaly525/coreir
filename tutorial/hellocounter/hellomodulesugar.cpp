#include "coreir.h"

using namespace CoreIR;

int main() {

  Context* c = newContext();

  Type* CounterType = c->Record({
    {"en",c->BitIn()}, 
    {"out",c->Bit()->Arr(16)}, //Convenient Arr Type Constructor
    {"clk",c->Named("coreir.clkIn")}, //Named Ref constructor 
  });

  //Now lets create a module declaration. Declarations are specified separately from the definition
  Module* counter = c->getGlobal()->newModuleDecl("counter",CounterType); //use getGlobalFunction
  ModuleDef* def = counter->newModuleDef();
    Args wArg({{"width",c->argInt(16)}});
    def->addInstance("ai","coreir.add",wArg); // using <namespace>.<module> notation 
    def->addInstance("ci","coreir.const",wArg,{{"value",c->argInt(1)}});

    //Reg has default arguments. en/clr/rst are False by default. Init is also 0 by default
    def->addInstance("ri","coreir.reg",{{"width",c->argInt(16)},{"en",c->argBool(true)}});
    
    //Connections
    def->connect("self.clk","ri.clk");
    def->connect("self.en","ri.en");
    def->connect("ci.out","ai.in0");
    def->connect("ai.out","ri.in");
    def->connect("ri.out","ai.in1");
    def->connect("ri.out","self.out");

  counter->setDef(def);
  counter->print();
  
  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
