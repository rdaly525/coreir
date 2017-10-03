#ifndef COREIR_NAMESPACE_HPP_
#define COREIR_NAMESPACE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class Namespace {
  Context* c;
  std::string name;

  std::map<std::string,Module*> moduleList;
  std::map<std::string,Generator*> generatorList;
  
  //Lists the named type without args
  std::map<std::string,NamedType*> namedTypeList;
  
  //Mapping name to typegen 
  std::map<std::string,TypeGen*> typeGenList;
  
  //Caches the NamedTypes with args
  std::unordered_map<std::string,std::unordered_map<Args,NamedType*>> namedTypeGenCache;

  //Save the unflipped names for json file
  std::unordered_map<std::string,std::string> namedTypeNameMap;
  std::unordered_map<std::string,std::string> typeGenNameMap;

  public :
    Namespace(Context* c, std::string name) : c(c), name(name) {}
    ~Namespace();
    const std::string& getName() { return name;}
    Context* getContext() { return c;}
    std::map<std::string,Module*> getModules() { return moduleList;}
    std::map<std::string,Generator*> getGenerators() { return generatorList;}

    NamedType* newNamedType(std::string name, std::string nameFlip, Type* raw);
    void newNominalTypeGen(std::string name, std::string nameFlip,Params genparams, TypeGenFun fun);
    TypeGen* newTypeGen(std::string name, Params genparams, std::string moduleName, std::string functionName);
    TypeGen* newTypeGen(std::string name, Params genparams, TypeGenFun fun);
    bool hasNamedType(std::string name);
    
    //Only returns named types without args
    std::map<std::string,NamedType*> getNamedTypes() { return namedTypeList;}
    NamedType* getNamedType(std::string name);
    NamedType* getNamedType(std::string name, Args genargs);
    TypeGen* getTypeGen(std::string name);
    bool hasTypeGen(std::string name) {return typeGenList.count(name)>0;}

    
    Generator* newGeneratorDecl(std::string name,TypeGen* typegen, Params genparams, Params configparams=Params());
    Module* newModuleDecl(std::string name, Type* t,Params configparams=Params());
    void addModule(Module* m);

    Generator* getGenerator(std::string gname);
    Module* getModule(std::string mname);
    Instantiable* getInstantiable(std::string name);
    bool hasModule(std::string mname) { return moduleList.count(mname) > 0; }
    bool hasGenerator(std::string iname) { return generatorList.count(iname) > 0; }
    bool hasInstantiable(std::string iname) { return moduleList.count(iname) > 0 || generatorList.count(iname) > 0; }
    
    void print();
};

}//CoreIR namespace

#endif //NAMESPACE_HPP_
