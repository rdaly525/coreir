#include "wireable.hpp"

using namespace std;

///////////////////////////////////////////////////////////
//----------------------- Wireables ----------------------//
///////////////////////////////////////////////////////////


namespace CoreIR {

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

Context* Wireable::getContext() { return moduledef->getContext();}


string Interface::toString() const{
  return "self";
}

string Instance::toString() const {
  return instname;
}

Arg* Instance::getConfigValue(string s) { 
  return config.at(s);
}

bool Instance::isGen() { return instRef->isKind(GEN);}
bool Instance::hasDef() { return instRef->hasDef(); }
void Instance::replace(Instantiable* _instRef, Args _config) {
  this->moduledef->getModule()->logInstanceDel(instRef->getNamespace()->getName(),instRef->getName());
  this->instRef = _instRef;
  this->config = _config;
  this->moduledef->getModule()->logInstanceAdd(_instRef->getNamespace()->getName(),_instRef->getName());
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

} //CoreIR namesapce
