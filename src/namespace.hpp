#ifndef NAMESPACE_HPP_
#define NAMESPACE_HPP_

#include <string>
#include <map>
#include "types.hpp" // For NamedType
#include "instantiable.hpp"
#include "common.hpp"
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {

struct GenCacheParams {
  Generator* g;
  Args ga;
  GenCacheParams(Generator* g, Args ga) : g(g), ga(ga) {}
  friend bool operator==(const GenCacheParams & l,const GenCacheParams & r);
};

struct GenCacheParamsHasher {
  size_t operator()(const GenCacheParams& gcp) const;
};

struct NamedCacheParams {
  string name;
  Args args;
  NamedCacheParams(string name, Args args) : name(name), args(args) {}
  friend bool operator==(const GenCacheParams & l,const GenCacheParams & r);
};

struct NamedCacheParamsHasher {
  size_t operator()(const NamedCacheParams& n) const;
};

class Namespace {
  Context* c;
  string name;

  unordered_map<GenCacheParams,Module*,GenCacheParamsHasher> genCache;

  unordered_map<string,Module*> moduleList;
  unordered_map<string,Generator*> generatorList;
  unordered_map<NamedCacheParams,NamedType*,NamedCacheParamsHasher> namedCache;
  
  //TODO slightly hacky
  //Mapping name to typegen and nameFlip
  unordered_map<string,std::pair<TypeGen,string>> typeGenList;

  public :
    Namespace(Context* c, string name) : c(c), name(name) {}
    ~Namespace();
    string getName() { return name;}
    Context* getContext() { return c;}
    unordered_map<string,Module*> getModules() { return moduleList;}
    unordered_map<string,Generator*> getGenerators() { return generatorList;}

    void newNamedType(string name, string nameFlip, Type* raw);
    void newNamedType(string name, string nameFlip, TypeGen typegen);
    NamedType* getNamedType(string name);
    NamedType* getNamedType(string name, Args genargs);
    TypeGen getTypeGen(string name);

    Generator* newGeneratorDecl(string name, Params kinds, TypeGen tg);
    Module* newModuleDecl(string name, Type* t,Params configparams=Params());

    Generator* getGenerator(string gname);
    Module* getModule(string mname);
    Instantiable* getInstantiable(string name);
    bool hasModule(string mname) { return moduleList.count(mname) > 0; }
    bool hasInstantiable(string iname) { return moduleList.count(iname) > 0 || generatorList.count(iname) > 0; }
    
    Module* runGenerator(Generator* g, Args ga, Type* t);
    json toJson();
    void print();
};

Namespace* newNamespace(Context* c,string name);

}//CoreIR namespace

#endif //NAMESPACE_HPP_
