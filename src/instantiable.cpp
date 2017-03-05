#ifndef INSTANTIABLE_CPP_
#define INSTANTIABLE_CPP_

//#include "enums.hpp"
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
Generator::Generator(CoreIRContext* c,string name,ArgKinds argkinds, TypeGen* typegen) : Instantiable(GEN,c,"",name), argkinds(argkinds), typegen(typegen), genfun(nullptr) {
  //Verify that argkinds are the same
  assert(argkinds == typegen->argkinds);
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    ArgKinds: " + ArgKinds2Str(argkinds);
  ret = ret + "\n    TypeGen: " + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

Module::~Module() {
  if (def) delete def;
}

string Module::toString() const {
  return "Module: " + name + "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

void Module::print(void) {
  cout << toString() << endl;
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
  cout << "  Def:" << endl;
  cout << "    Instances:" << endl;
  for (auto inst : instances) {
    cout << "      " << (*inst) << endl;
  }
  cout << "    Wirings:\n";
  for (auto wiring : wirings) {
    cout << "      " << *(wiring.first) << " <=> " << *(wiring.second) << endl ;
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

bool checkWiring(Wireable* a, Wireable* b) {
  CoreIRContext* c = a->getContext();
  Type* ta = a->getType();
  Type* tb = b->getType();
  
  //TODO This might not be valid if:
  //  2 outputs are connected to the same input
  //  an inout is connected to an input (good!)
  //  an inout is connected to an output (bad!)
  
  if (ta->isKind(ANY) || tb->isKind(ANY)) return true;
  if (ta == c->Flip(tb) ) return true;
  
  c->newerror();
  c->error("Cannot wire together");
  c->error("  " + a->toString() + " : " + a->getType()->toString());
  c->error("  " + b->toString() + " : " + b->getType()->toString());
  return false;
}

void ModuleDef::wire(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same context
  CoreIRContext* c = getContext();
  if (a->getModuleDef()!=this || b->getModuleDef() != this) {
    c->newerror();
    c->error("Wirings can only occur within the same module");
    c->error("  This ModuleDef: " + module->getName());
    c->error("  ModuleDef of " + a->toString() + ": " + a->getModuleDef()->getName());
    c->error("  ModuleDef of " + b->toString() + ": " + b->getModuleDef()->getName());
    return;
  }

  //TODO what if we connect the same wires together
  checkWiring(a,b);
    
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
  CoreIRContext* c = getContext();
  Type* ret = c->Any();
  bool error = type->sel(c,selStr,&ret);
  if (error) {
    c->error("  Wire: " + toString());
  }
  return moduledef->getCache()->newSelect(moduledef,this,selStr,ret);
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

string Interface::toString() const{
  return moduledef->getName();
}

string Instance::toString() const {
  return instname;
}
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
