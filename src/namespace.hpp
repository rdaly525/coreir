#ifndef NAMESPACE_HPP_
#define NAMESPACE_HPP_

#include <string>
#include <map>
#include "types.hpp" // For TypeGen
#include "instantiable.hpp"
#include "common.hpp"

using namespace std;

class Namespace {
  Context* c;
  string name;

  map<string,Module*> mList;
  map<string,Generator*> gList;
  map<string,TypeGen*> tList;
  
  public :
    Namespace(Context* c, string name) : c(c), name(name) {}
    ~Namespace();
    string getName() { return name;}
    Context* getContext() { return c;}
    map<string,Module*> getModules() { return mList;}
    map<string,Generator*> getGenerators() { return gList;}
    map<string,TypeGen*> getTypeGens() { return tList;}

    TypeGen* newTypeGen(string name, string nameFlipped, ArgKinds kinds, TypeGenFun fun);
    TypeGen* getTypeGen(string name) {
      assert(hasTypeGen(name));
      return tList.find(name)->second;
    }
    bool hasTypeGen(string name) {
      return tList.find(name) != tList.end();
    }
    
    Generator* newGeneratorDecl(string name, ArgKinds kinds, TypeGen* tg);
    Module* newModuleDecl(string name, Type* t);

    Generator* getGenerator(string gname);
    Module* getModule(string mname);

    void print();
};

Namespace* newNamespace(Context* c,string name);

#endif //NAMESPACE_HPP_
