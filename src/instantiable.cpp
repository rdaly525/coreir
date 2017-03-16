#ifndef INSTANTIABLE_CPP_
#define INSTANTIABLE_CPP_

#include <cassert>
#include <vector>
#include <set>

#include "instantiable.hpp"


using namespace std;


size_t std::hash<CoreIR::Connection>::operator() (const CoreIR::Connection& c) const {
  size_t hash;
  hash_combine(hash,c.first);
  hash_combine(hash,c.second);
  return hash;
}




namespace CoreIR {
///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////
Context* Instantiable::getContext() { return ns->getContext();}

bool operator==(const Instantiable & l,const Instantiable & r) {
  return l.isKind(r.getKind()) && (l.getName()==r.getName()) && (l.getNamespace()->getName() == r.getNamespace()->getName());
}

Module* Instantiable::toModule() {
  if (isKind(MOD)) return (Module*) this;
  Error e;
  e.message("Cannot convert to a Module!!");
  e.message("  " + toString());
  e.fatal();
  getContext()->error(e);
  return nullptr;
}
Generator* Instantiable::toGenerator() {
  if (isKind(GEN)) return (Generator*) this;
  Error e;
  e.message("Cannot convert to a Generator!!");
  e.message("  " + toString());
  e.fatal();
  getContext()->error(e);
  return nullptr;
}

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}

Generator::Generator(Namespace* ns,string name,Params genparams, TypeGen* typegen, Params configparams) : Instantiable(GEN,ns,name,configparams), genparams(genparams), typegen(typegen), genfun(nullptr) {
  //Verify that genparams are the same
  assert(genparams == typegen->genparams);
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + Params2Str(genparams);
  ret = ret + "\n    TypeGen: " + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

Module::~Module() {
  
  for (auto md : mdefList) delete md;
}

string Module::toString() const {
  return "Module: " + name + "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

void Module::print(void) {
  cout << toString() << endl;
  if(def) def->print();

}
ModuleDef* Module::newModuleDef() {
  
  ModuleDef* md = new ModuleDef(this);
  mdefList.push_back(md);
  return md;
}

ModuleDef::ModuleDef(Module* module) : module(module) {
  interface = new Interface(this,module->getContext()->Flip(module->getType()));
  cache = new SelCache();
}

ModuleDef::~ModuleDef() {
  //Delete interface, instances, cache
  delete interface;
  for(auto inst : instances) delete inst.second;
  delete cache;
}


void ModuleDef::print(void) {
  cout << "  Def:" << endl;
  cout << "    Instances:" << endl;
  for (auto inst : instances) {
    cout << "      " << inst.first << " : " << inst.second->getInstRef()->getName() << endl;
  }
  cout << "    Connections:\n";
  for (auto connection : connections) {
    cout << "      " << *(connection.first) << " <=> " << *(connection.second) << endl ;
  }
  cout << endl;
}

Instance* ModuleDef::addInstance(string instname,Generator* gen, Args* args,Args* config) {
  //Should this type be resolved? Just create a typeGenInst for now
  Context* c = gen->getContext();
  Type* type = c->TypeGenInst(gen->getTypeGen(),args);
  
  Instance* inst = new Instance(this,instname,gen,type,args,config);
  instances[instname] = inst;
  return inst;
}

Instance* ModuleDef::addInstance(string instname,Module* m,Args* config) {
  Instance* inst = new Instance(this,instname,m,m->getType(),nullptr,config);
  instances[instname] = inst;
  return inst;
}

Instance* ModuleDef::addInstance(Instance* i) {
  if( i->getInstRef()->isKind(MOD)) 
    return addInstance(i->getInstname(),(Module*) i->getInstRef(),i->getConfig());
  else 
    return addInstance(i->getInstname(),(Generator*) i->getInstRef(),i->getConfig(),i->getArgs());
}


void ModuleDef::wire(Wireable* a, Wireable* b) {
  //Make sure you are connecting within the same context
  Context* c = getContext();
  if (a->getModuleDef()!=this || b->getModuleDef() != this) {
    Error e;
    e.message("connections can only occur within the same module");
    e.message("  This ModuleDef: " + module->getName());
    e.message("  ModuleDef of " + a->toString() + ": " + a->getModuleDef()->getName());
    e.message("  ModuleDef of " + b->toString() + ": " + b->getModuleDef()->getName());
    c->error(e);
    return;
  }

  // TODO should I type check here at all?
  //checkWiring(a,b);
  //Update 'a' and 'b'
  a->addConnectedWireable(b);
  b->addConnectedWireable(a);
  
  Connection connect(a,b);
  //Insert into set of wireings 
  //minmax gauranees an ordering
  connections.insert(connect);
}

void ModuleDef::wire(WirePath pathA, WirePath pathB) {
  Wireable* curA = this->sel(pathA.first);
  Wireable* curB = this->sel(pathB.first);
  for (auto str : pathA.second) curA = curA->sel(str);
  for (auto str : pathB.second) curB = curB->sel(str);
  this->wire(curA,curB);
}


Wireable* ModuleDef::sel(string s) { 
  if (s=="self") return interface;
  else return instances[s]; 
}

///////////////////////////////////////////////////////////
//----------------------- Wireables ----------------------//
///////////////////////////////////////////////////////////


Select* Wireable::sel(string selStr) {
  Context* c = getContext();
  Type* ret = c->Any();
  Error e;
  bool error = type->sel(c,selStr,&ret,&e);
  if (error) {
    e.message("  Wire: " + toString());
    //e.fatal();
    getContext()->error(e);
  }
  Select* select = moduledef->getCache()->newSelect(moduledef,this,selStr,ret);
  selects.emplace(selStr,select);
  return select;
}

Select* Wireable::sel(uint selStr) { return sel(to_string(selStr)); }

// TODO This might be slow due to insert on a vector. Maybe use Deque?
WirePath Wireable::getPath() {
  Wireable* top = this;
  vector<string> path;
  while(top->isKind(SEL)) {
    Select* s = (Select*) top;
    path.insert(path.begin(), s->getSelStr());
    top = s->getParent();
  }
  if (top->isKind(IFACE)) return {"self",path};
  string instname = ((Instance*) top)->getInstname();
  return {instname, path};
}



string Interface::toString() const{
  return "self";
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

}//CoreIR namespace

#endif //COREIR_CPP_
