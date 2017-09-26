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

  //Test casting of ArgBool
  {
    ArgPtr a = Const(false);
    assert(isa<ArgBool>(a));
    assert(a->get<bool>()==false);
    shared_ptr<ArgBool> ac = cast<ArgBool>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgBool>(a));
    assert(!dyn_cast<ArgString>(a));
  }
  
  //Test casting of ArgInt
  {
    ArgPtr a = Const(5);
    assert(isa<ArgInt>(a));
    assert(a->get<int>()==5);
    shared_ptr<ArgInt> ac = cast<ArgInt>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgInt>(a));
    assert(!dyn_cast<ArgString>(a));
  }
  
  //Test casting of ArgString
  {
    ArgPtr a = Const("Ross");
    assert(isa<ArgString>(a));
    assert(a->get<string>()=="Ross");
    shared_ptr<ArgString> ac = cast<ArgString>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgString>(a));
    assert(!dyn_cast<ArgType>(a));
  }
  
  //Test casting of ArgType
  {
    ArgPtr a = Const(c->BitIn());
    assert(isa<ArgType>(a));
    assert(a->get<Type*>()==c->BitIn());
    shared_ptr<ArgType> ac = cast<ArgType>(a);
    assert(dyn_cast<Arg>(ac));
    assert(dyn_cast<ArgType>(a));
    assert(!dyn_cast<ArgInt>(a));
  }

  //Test casting of Module
  {
    Namespace* g = c->getGlobal();
    Instantiable* m = g->newModuleDecl("A",c->Record());
    assert(isa<Module>(m));
    Module* mi = cast<Module>(m);
    assert(dyn_cast<Instantiable>(m));
    assert(dyn_cast<Module>(mi));
    assert(!dyn_cast<Generator>(mi));
  }
  
  //Test casting of Generator
  {
    Namespace* coreir = c->getNamespace("coreir");
    Instantiable* m = coreir->getGenerator("add");
    assert(isa<Generator>(m));
    Generator* mi = cast<Generator>(m);
    assert(dyn_cast<Instantiable>(m));
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
