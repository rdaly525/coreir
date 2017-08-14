#include "coreir.h"

using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* stdlib = c->getNamespace("stdlib");
 
  //Type of module 
  Type* addmultType = c->Record({
    {"in",c->Array(16,c->BitIn())},
    {"out",c->Array(16,c->Bit())}
  });
  Args w16({{"width",c->argInt(16)}});
  Generator* Add = stdlib->getGenerator("add");
  Generator* Mul = stdlib->getGenerator("mul");
  Generator* Const = stdlib->getGenerator("const");
  Module* addmult = c->getGlobal()->newModuleDecl("addmult",addmultType);
  ModuleDef* def = addmult->newModuleDef();
    def->addInstance("ai",Add,w16);
    def->addInstance("mi",Mul,w16);
    def->addInstance("ci",Const,w16,{{"value",c->argInt(140)}});
    
    def->connect("self.in","ai.in.0");
    def->connect("ci.out","ai.in.1");
    def->connect("ci.out","mi.in.0");
    def->connect("ai.out","mi.in.1");
    def->connect("mi.out","self.out");
  addmult->setDef(def);

  addmult->print();
  
  deleteContext(c);
  return 0;
}
