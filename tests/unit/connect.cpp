#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  
  Namespace* coreir = c->getNamespace("coreir");
  
  Module* const16 = coreir->getGenerator("const")->getModule({{"width",Const::make(c,16)}});
 
  // Define Module Type
  Type* mType = c->Record({
      {"out",c->Array(16,c->Bit())}
  });
    
  Module* mod = g->newModuleDecl("mod",mType);
  ModuleDef* def = mod->newModuleDef();
    Wireable* self = def->sel("self");
    Wireable* i0 = def->addInstance("i0",const16,{{"value",Const::make(c,BitVector(16,23))}});
    def->connect(i0->sel("out"),self->sel("out"));
    assert(def->hasConnection(i0->sel("out"),self->sel("out")));
    assert(def->hasConnection(self->sel("out"),i0->sel("out")));
    //Also check other wiring syntax 
    def->disconnect(i0->sel("out"),self->sel("out"));
    def->connect("self.out","i0.out");
    def->disconnect(i0->sel("out"),self->sel("out"));
    def->connect({"self","out"},{"i0","out"});
    def->disconnect(i0->sel("out"),self->sel("out"));
    def->connect({string("self"),string("out")},{string("i0"),string("out")});
  mod->setDef(def);
 
  //Verify that the number of connections is only 1. 
  assert(def->getConnections().size() == 1);

  //Delete that connection and verify that it is 0
  def->disconnect(i0->sel("out"),self->sel("out"));
  def->validate();
  assert(def->getConnections().size() == 0);
  mod->print();

  def->connect("self.out","i0.out");
  def->validate();
  assert(def->getConnections().size() == 1);
  mod->print();

  def->removeInstance("i0");
  def->validate();
  assert(def->getConnections().size() == 0);
  assert(def->getInstances().size() == 0);
  mod->print();

  deleteContext(c);
  
  return 0;
}
