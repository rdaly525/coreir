#ifndef COREIR_NAMESPACE_HPP_
#define COREIR_NAMESPACE_HPP_

#include "fwd_declare.h"
#include "common.h"

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
  std::map<std::string,std::map<Values,NamedType*,ValuesComp>> namedTypeGenCache;

  //Save the unflipped names for json file
  std::map<std::string,std::string> namedTypeNameMap;
  std::map<std::string,std::string> typeGenNameMap;

  public :
    Namespace(Context* c, std::string name);
    ~Namespace();
    const std::string& getName() { return name;}
    Context* getContext() { return c;}
    //Returns a map of ALL modules including generated ones
    //for generated mdules, the key is the uniquified longname
    std::map<std::string,Module*> getModules(bool includeGenerated=true);
    const std::map<std::string,Generator*>& getGenerators() { return generatorList;}

    NamedType* newNamedType(std::string name, std::string nameFlip, Type* raw);
    void newNominalTypeGen(std::string name, std::string nameFlip,Params genparams, TypeGenFun fun);
    
    bool hasNamedType(std::string name);
    
    //Only returns named types without args
    //TODO depreciate Named Types with args
    std::map<std::string,NamedType*> getNamedTypes() { return namedTypeList;}
    NamedType* getNamedType(std::string name);
    NamedType* getNamedType(std::string name, Values genargs);
    
    //This is transferring control of typegen to Namespace
    void addTypeGen(TypeGen* typegen);
    //TODO depreciate the following function
    TypeGen* newTypeGen(std::string name, Params genparams, TypeGenFun fun);
    TypeGen* getTypeGen(std::string name);
    const std::map<std::string,TypeGen*>& getTypeGens() { return typeGenList; }
    bool hasTypeGen(std::string name) {return typeGenList.count(name)>0;}

    Generator* newGeneratorDecl(std::string name,TypeGen* typegen, Params genparams);
    Module* newModuleDecl(std::string name, Type* t,Params moduleparams=Params());

    //Use with caution!!
    //This will also delete all modules in generator
    void eraseGenerator(std::string name);
    void eraseModule(std::string name);

    Generator* getGenerator(std::string gname);
    Module* getModule(std::string mname);
    GlobalValue* getGlobalValue(std::string name);
    bool hasModule(std::string mname) { return moduleList.count(mname) > 0; }
    bool hasGenerator(std::string iname) { return generatorList.count(iname) > 0; }
    bool hasGlobalValue(std::string iname) { return moduleList.count(iname) > 0 || generatorList.count(iname) > 0; }
    
    void print();
};

}//CoreIR namespace

#endif //NAMESPACE_HPP_
