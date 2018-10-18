#include "coreir/ir/typegen.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/common.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/generator.h"

using namespace std;

namespace CoreIR {


Type* TypeGen::getType(Values args) {
  if (typeCache.count(args)) {
    return typeCache.at(args);
  }
  checkValuesAreParams(args,params);
  try {
    Type* t = this->createType(args);
    assert(t);
    if (flipped) {
      t = t->getFlipped();
    }
    typeCache[args] = t;
    return t;
  }
  catch(const std::out_of_range&) {
    cout << "Failed on " << this->getRefName() << " with args=" << ::CoreIR::toString(args) << endl;
    assert(0);
    return nullptr;
  }
}

bool TypeGenFromFun::hasType(Values genargs) {
  return doValuesMatchParams(genargs,this->getParams());
}

std::string TypeGenFromFun::toString() const {
  return this->getRefName() + ::CoreIR::toString(this->getParams());
}

TypeGenFromFun* TypeGenFromFun::make(Namespace* ns, std::string name, Params genparams, TypeGenFun fun, bool flipped) {
  
  TypeGenFromFun* tg = new TypeGenFromFun(ns,name,genparams,fun,flipped);
  ns->addTypeGen(tg);
  return tg;

}

TypeGenSparse::TypeGenSparse(Namespace* ns, std::string name, Params params, std::vector<std::pair<Values,Type*>>& typelist) : TypeGen(ns,name,params,false) {
  for (auto vpair : typelist) {
    ASSERT(typeLookup.count(vpair.first)==0,"In " + this->toString() + " Cannot add duplicate " + ::CoreIR::toString(vpair.first));
    checkValuesAreParams(vpair.first,this->getParams());
    typeLookup[vpair.first] = vpair.second;
  }
}

bool TypeGenSparse::hasType(Values genargs) {
  return typeLookup.count(genargs) > 0;
}

Type* TypeGenSparse::createType(Values genargs) {
  if (typeLookup.count(genargs)) {
    return typeLookup[genargs];
  }
  ASSERT(0,"Typegen: " + this->toString() + " cannot handle args=" + ::CoreIR::toString(genargs));
}

std::string TypeGenSparse::toString() const {
  return this->getRefName() + ::CoreIR::toString(this->getParams());
}

TypeGenSparse* TypeGenSparse::make(Namespace* ns, std::string name, Params params, std::vector<std::pair<Values,Type*>>& typelist) {
  TypeGenSparse* tg = new TypeGenSparse(ns,name,params,typelist);
  ns->addTypeGen(tg);
  return tg;
}

bool TypeGenImplicit::hasType(Values genargs) {
  return false;
}

Type* TypeGenImplicit::createType(Values genargs) {
  ASSERT(0,"Cannot ever create a type with a TypeGenImplicit");
}

std::string TypeGenImplicit::toString() const {
  return this->getRefName() + ::CoreIR::toString(this->getParams());
}

TypeGenImplicit* TypeGenImplicit::make(Namespace* ns, std::string name, Params params) {
  TypeGenImplicit* tg = new TypeGenImplicit(ns,name,params);
  ns->addTypeGen(tg);
  return tg;
}

}
