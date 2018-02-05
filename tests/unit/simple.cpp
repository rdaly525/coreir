#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  //Type of module 
  Type* addmultType = c->Record({
    {"in",c->Array(16,c->BitIn())},
    {"out",c->Array(16,c->Bit())}
  });
  Values w16({{"width",Const::make(c,16)}});
  Module* addmult = c->getGlobal()->newModuleDecl("addmult",addmultType);
  ModuleDef* def = addmult->newModuleDef();
    def->addInstance("ai","coreir.add",w16);
    def->addInstance("mi","coreir.mul",w16);
    def->addInstance("ci","coreir.const",w16,{{"value",Const::make(c,BitVector(16,140))}});

    def->connect("self.in","ai.in0");
    def->connect("ci.out","ai.in1");
    def->connect("ci.out","mi.in0");
    def->connect("ai.out","mi.in1");
    def->connect("mi.out","self.out");
  addmult->setDef(def);

  addmult->print();
  cout << addmult->toString() << endl;
  
  deleteContext(c);
  return 0;
}
