#ifndef INSTANTIABLE_CPP_
#define INSTANTIABLE_CPP_

#include "enums.hpp"
#include <cassert>
#include <vector>
#include <set>
#include "instantiable.hpp"

using namespace std;

///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}
Generator::Generator(CoreIRContext* c,string name,ArgKinds argkinds, TypeGen* typegen) : Instantiable(GEN,c,"",name), argkinds(argkinds), typegen(typegen) {
  //Verify that argkinds are the same
  assert(argkinds == typegen->argkinds);
}

void Module::print(void) {
  cout << toString() << endl;
  cout << "NYI" << endl;
  if(def) def->print();
}
ModuleDef* Module::newModuleDef() {
  return new ModuleDef(this);
}

ModuleDef::ModuleDef(Module* module) : module(module) {
  interface = new Interface(this,module->getContext()->Flip(module->getType()));
  cache = new SelCache();
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(auto inst : instances) delete inst;
  delete cache;
}


void ModuleDef::print(void) {
  cout << "ModuleDef: " << module->getName() << "\n";
  cout << "  Type: " << (*module->getType()) << "\n";
  cout << "  Instances:\n";
  for (auto inst : instances) {
    cout << "    " << (*inst) << endl;
  }
  cout << "  Wirings:\n";
  for (auto wiring : wirings) {
    cout << "    " << *(wiring.first) << " <=> " << *(wiring.second) << "\n" ;
  }
  cout << endl;
}

Instance* ModuleDef::addInstanceGenerator(string instname,Generator* gen, GenArgs* args) {
  //Should this type be resolved? Just create a typeGenInst for now
  CoreIRContext* c = gen->getContext();
  Type* type = c->TypeGenInst(gen->getTypeGen(),args);
  
  Instance* inst = new Instance(this,instname,gen,type,args);
  instances.insert(inst);
  return inst;
}

Instance* ModuleDef::addInstanceModule(string instname,Module* m) {
  Instance* inst = new Instance(this,instname,m,m->getType(),nullptr);
  instances.insert(inst);
  return inst;
}

void ModuleDef::wire(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same context
  if (a->getContext()!=this || b->getContext() != this) {
    cout << "ERROR: Wirings can only occur within the same module\n";
    cout << "  This ModuleDef: "  << module->getName() << endl;
    cout << "  ModuleDef of " <<a->toString() << ": " << a->getContext()->module->getName() << endl;
    cout << "  ModuleDef of " <<b->toString() << ": " << b->getContext()->module->getName() << endl;
    exit(0);
  }
  
  //Update 'a' and 'b'
  a->addWiring(b);
  b->addWiring(a);
 
  //Insert into set of wireings 
  //minmax gauranees an ordering
  wirings.insert(std::minmax(a,b));
}

///////////////////////////////////////////////////////////
//----------------------- Wireables ----------------------//
///////////////////////////////////////////////////////////

Select* Wireable::sel(string selStr) {
  cout << "Selecting " << selStr << " from Wireable with type: " << *type << endl;
  CoreIRContext* c = context->getContext();
  Type* ret = c->Any();
  bool error = type->sel(c,selStr,&ret);
  cout << "sel:" << selStr << " : " << *type << endl;
  assert(!error);
  cout << "  SUCCESS: " << *ret << endl;
  return context->getCache()->newSelect(context,this,selStr,ret);
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

string Interface::toString() const{
  return context->getName();
}

string Instance::toString() const {
  return instname;
}
Instance::~Instance() {if(genargs) delete genargs;}
string Select::toString() const {
  string ret = parent->toString(); 
  if (isNumber(selStr)) return ret + "[" + selStr + "]";
  return ret + "." + selStr;
}

std::ostream& operator<<(ostream& os, const Wireable& i) {
  os << i.toString();
  return os;
}

///////////////////////////////////////////////////////////
//-------------------- SelCache --------------------//
///////////////////////////////////////////////////////////

SelCache::~SelCache() {
  for (auto sel : cache) delete sel.second;
}

Select* SelCache::newSelect(ModuleDef* context, Wireable* parent, string selStr, Type* type) {
  SelectParamType params = {parent,selStr};
  auto it = cache.find(params);
  if (it != cache.end()) {
    assert(it->second->getType() == type);
    return it->second;
  } 
  else {
    Select* s = new Select(context,parent,selStr, type);
    cache.emplace(params,s);
    return s;
  }
}


#endif //COREIR_CPP_
