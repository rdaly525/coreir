#ifndef NAMESPACE_HPP_
#define NAMESPACE_HPP_

#include "types.hpp" // For NamedType
#include "instantiable.hpp"
#include "common.hpp"
#include "json.hpp"
#include "property.hpp"
#include <string>
#include <map>

using json = nlohmann::json;
using namespace std;

namespace CoreIR {

struct NamedCacheParams {
  string name;
  Args args;
  NamedCacheParams(string name, Args args) : name(name), args(args) {}
  friend bool operator==(const NamedCacheParams & l,const NamedCacheParams & r);
};

struct NamedCacheParamsHasher {
  size_t operator()(const NamedCacheParams& n) const;
};

class Namespace {
  Context* c;
  string name;

  unordered_map<string,Module*> moduleList;
  unordered_map<string,Generator*> generatorList;
  
  
  //Lists the named type without args
  unordered_map<string,NamedType*> namedTypeList;
  
  //Caches the NamedTypes with args
  unordered_map<NamedCacheParams,NamedType*,NamedCacheParamsHasher> namedTypeGenCache;
  
  //Mapping name to typegen 
  unordered_map<string,TypeGen*> typeGenList;

  //Save the unflipped names for json file
  unordered_map<string,string> namedTypeNameMap;
  unordered_map<string,string> typeGenNameMap;

  Property property;
  
  public :
    Namespace(Context* c, string name) : c(c), name(name) {}
    ~Namespace();
    const string& getName() { return name;}
    Context* getContext() { return c;}
    unordered_map<string,Module*> getModules() { return moduleList;}
    unordered_map<string,Generator*> getGenerators() { return generatorList;}

    NamedType* newNamedType(string name, string nameFlip, Type* raw);
    void newNominalTypeGen(string name, string nameFlip,Params genparams, TypeGenFun fun);
    TypeGen* newTypeGen(string name, Params genparams, TypeGenFun fun);
    bool hasNamedType(string name);
    
    //Only returns named types without args
    unordered_map<string,NamedType*> getNamedTypes() { return namedTypeList;}
    NamedType* getNamedType(string name);
    NamedType* getNamedType(string name, Args genargs);
    TypeGen* getTypeGen(string name);
    bool hasTypeGen(string name) {return typeGenList.count(name)>0;}

    
    Generator* newGeneratorDecl(string name,TypeGen* typegen, Params genparams, Params configparams=Params());
    Module* newModuleDecl(string name, Type* t,Params configparams=Params());
    void addModule(Module* m);

    Generator* getGenerator(string gname);
    Module* getModule(string mname);
    Instantiable* getInstantiable(string name);
    bool hasModule(string mname) { return moduleList.count(mname) > 0; }
    bool hasGenerator(string iname) { return generatorList.count(iname) > 0; }
    bool hasInstantiable(string iname) { return moduleList.count(iname) > 0 || generatorList.count(iname) > 0; }

    void setProperty(json j) {property.setJson(j);}
    Property getProperty() {return property;}
  
    json toJson();
    void print();
};

Namespace* newNamespace(Context* c,string name);

}//CoreIR namespace

#endif //NAMESPACE_HPP_
