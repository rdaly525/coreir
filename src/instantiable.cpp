#include <cassert>
#include <vector>
#include <set>

#include "instantiable.hpp"

using namespace std;

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

Generator::Generator(Namespace* ns,string name,Params genparams, TypeGen typegen, Params configparams) : Instantiable(GEN,ns,name,configparams), genparams(genparams), typegen(typegen), genfun(nullptr) {
  //Verify that genparams are a superset of typegen params
  for (auto const &type_param : typegen.params) {
	  auto const &gen_param = genparams.find(type_param.first);
	  assert(gen_param != genparams.end());
	  assert(gen_param->second == type_param.second);
  }
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + Params2Str(genparams);
  ret = ret + "\n    TypeGen: TODO";// + typegen->toString();
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

}//CoreIR namespace
