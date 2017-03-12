#ifndef NAMESPACE_HPP_
#define NAMESPACE_HPP_

#include <string>
#include <map>
#include "types.hpp" // For TypeGen
#include "instantiable.hpp"
#include "common.hpp"
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

struct GenCacheParams {
  Generator* g;
  GenArgs* ga;
  GenCacheParams(Generator* g, GenArgs* ga) : g(g), ga(ga) {}
  friend bool operator==(const GenCacheParams & l,const GenCacheParams & r);
  friend bool operator!=(const GenCacheParams & l,const GenCacheParams & r);

};

struct GenCacheParamsHasher {
  size_t operator()(const GenCacheParams& gcp) const;
};

class Namespace {
  Context* c;
  string name;

  unordered_map<GenCacheParams,Module*,GenCacheParamsHasher> genCache;

  unordered_map<string,Module*> mList;
  unordered_map<string,Generator*> gList;
  unordered_map<string,TypeGen*> tList;
  
  public :
    Namespace(Context* c, string name) : c(c), name(name) {}
    ~Namespace();
    string getName() { return name;}
    Context* getContext() { return c;}
    unordered_map<string,Module*> getModules() { return mList;}
    unordered_map<string,Generator*> getGenerators() { return gList;}
    unordered_map<string,TypeGen*> getTypeGens() { return tList;}

    TypeGen* newTypeGen(string name, string nameFlipped, GenParams kinds, TypeGenFun fun);
    TypeGen* getTypeGen(string name) {
      assert(hasTypeGen(name));
      return tList.find(name)->second;
    }
    bool hasTypeGen(string name) {
      return tList.find(name) != tList.end();
    }
    
    Generator* newGeneratorDecl(string name, GenParams kinds, TypeGen* tg);
    Module* newModuleDecl(string name, Type* t);

    Generator* getGenerator(string gname);
    Module* getModule(string mname);
    
    Module* runGenerator(Generator* g, GenArgs* ga);
    json toJson();
    void print();
};

Namespace* newNamespace(Context* c,string name);

#endif //NAMESPACE_HPP_
