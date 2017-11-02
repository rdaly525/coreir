#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  
  //Bit
  {
    Type* t = c->Bit();
    assert(isa<BitType>(t));
    BitType* at = cast<BitType>(t);
    assert(dyn_cast<Type>(at));
    assert(dyn_cast<BitType>(t));
    assert(!dyn_cast<RecordType>(t));
  }
  
  //Array
  {
    Type* t = c->Array(5,c->Array(3,c->BitIn()));
    assert(isa<ArrayType>(t));
    ArrayType* at = cast<ArrayType>(t);
    assert(dyn_cast<Type>(at));
    assert(dyn_cast<ArrayType>(t));
    assert(!dyn_cast<RecordType>(t));
  }

  //Test casting of ConstBool
  {
    Const* a = Const::make(c,false);
    assert(isa<ConstBool>(a));
    assert(a->get<bool>()==false);
    ConstBool* ac = cast<ConstBool>(a);
    assert(dyn_cast<Const>(ac));
    assert(dyn_cast<ConstBool>(a));
    assert(!dyn_cast<ConstString>(a));
  }
  
  //Test casting of ConstInt
  {
    Const* a = Const::make(c,5);
    assert(isa<ConstInt>(a));
    assert(a->get<int>()==5);
    ConstInt* ac = cast<ConstInt>(a);
    assert(dyn_cast<Const>(ac));
    assert(dyn_cast<ConstInt>(a));
    assert(!dyn_cast<ConstString>(a));
  }
  
  //Test casting of ConstString
  {
    Const* a = Const::make(c,"Ross");
    assert(isa<ConstString>(a));
    assert(a->get<string>()=="Ross");
    ConstString* ac = cast<ConstString>(a);
    assert(dyn_cast<Const>(ac));
    assert(dyn_cast<ConstString>(a));
    assert(!dyn_cast<ConstCoreIRType>(a));
  }
  
  //Test casting of ConstCoreIRType
  {
    Const* a = Const::make(c,c->BitIn());
    assert(isa<ConstCoreIRType>(a));
    assert(a->get<Type*>()==c->BitIn());
    ConstCoreIRType* ac = cast<ConstCoreIRType>(a);
    assert(dyn_cast<Const>(ac));
    assert(dyn_cast<ConstCoreIRType>(a));
    assert(!dyn_cast<ConstInt>(a));
  }

  //Test casting of Module
  {
    Namespace* g = c->getGlobal();
    GlobalValue* m = g->newModuleDecl("A",c->Record());
    assert(isa<Module>(m));
    Module* mi = cast<Module>(m);
    assert(dyn_cast<GlobalValue>(m));
    assert(dyn_cast<Module>(mi));
    assert(!dyn_cast<Generator>(mi));
  }
  
  //Test casting of Generator
  {
    Namespace* coreir = c->getNamespace("coreir");
    GlobalValue* m = coreir->getGenerator("add");
    assert(isa<Generator>(m));
    Generator* mi = cast<Generator>(m);
    assert(dyn_cast<GlobalValue>(m));
    assert(dyn_cast<Generator>(mi));
    assert(!dyn_cast<Module>(mi));
  }

  //Test casting of Wireables
  {
    Namespace* g = c->getGlobal();
    Module* m = g->newModuleDecl("B",c->Record({{"in",c->Bit()}}));
    ModuleDef* def = m->newModuleDef();
    Wireable* iface = def->sel("self");
    assert(isa<Interface>(iface));
    Interface* iface_ = cast<Interface>(iface);
    assert(dyn_cast<Wireable>(iface_));
    assert(dyn_cast<Interface>(iface));
    assert(!dyn_cast<Select>(iface));

    Wireable* inst = def->addInstance("i0",m);
    assert(isa<Instance>(inst));
    Instance* inst_ = cast<Instance>(inst);
    assert(dyn_cast<Wireable>(inst_));
    assert(dyn_cast<Instance>(inst));
    assert(!dyn_cast<Interface>(inst));
    
    Wireable* sel = inst->sel("in");
    assert(isa<Select>(sel));
    Select* sel_ = cast<Select>(sel);
    assert(dyn_cast<Wireable>(sel_));
    assert(dyn_cast<Select>(sel));
    assert(!dyn_cast<Instance>(sel));
  }

  deleteContext(c);

}
