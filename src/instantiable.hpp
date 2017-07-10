#ifndef INSTANTIABLE_HPP_
#define INSTANTIABLE_HPP_

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hpp"
#include "context.hpp"
#include "types.hpp"
#include "args.hpp"
#include "json.hpp"

#include "moduledef.hpp"
#include "generatordef.hpp"

#include "metadata.hpp"
#include "directedview.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {

class Instantiable {
  public :
    enum InstantiableKind {IK_Module,IK_Generator};
    enum LinkageKind {LK_Namespace, LK_Generated};
  protected:
    InstantiableKind kind;
    Namespace* ns;
    string name;
    Metadata metadata;
    Params configparams;
    Args defaultConfigArgs;
    LinkageKind linkageKind;
  public :
    Instantiable(InstantiableKind kind, Namespace* ns, string name, Params configparams) : kind(kind), ns(ns), name(name), configparams(configparams), linkageKind(LK_Namespace) {}
    virtual ~Instantiable() {}
    
    virtual bool hasDef() const=0;
    virtual string toString() const =0;
    bool isKind(InstantiableKind k) const { return kind==k;}
    InstantiableKind getKind() const { return kind;}
    void setLinkageKind(LinkageKind k) { linkageKind = k;}
    LinkageKind getLinkageKind() { return linkageKind; }
    Context* getContext();
    Params getConfigParams() { return configparams;}
    Metadata getMetadata() { return metadata;}
    const string& getName() const { return name;}
    //string getName() const { return name;}
    virtual json toJson()=0;
    Namespace* getNamespace() const { return ns;}
    void setNamespace(Namespace* ns) {this->ns = ns;}
    friend bool operator==(const Instantiable & l,const Instantiable & r);
    
    void setDefaultConfigArgs(Args defaultConfigArgs);
    Args getDefaultConfigArgs() { return defaultConfigArgs;}
};

std::ostream& operator<<(ostream& os, const Instantiable&);

class Generator : public Instantiable {
  TypeGen* typegen;
  Params genparams;
  Args defaultGenArgs; 
  //This is memory managed
  unordered_map<Args,Module*> genCache;
  GeneratorDef* def = nullptr;
  
  public :
    Generator(Namespace* ns,string name,TypeGen* typegen, Params genparams, Params configparams);
    ~Generator();
    static bool classof(const Instantiable* i) {return i->getKind()==IK_Generator;}
    string toString() const;
    json toJson();
    TypeGen* getTypeGen() const { return typegen;}
    bool hasDef() const { return !!def; }
    GeneratorDef* getDef() const {return def;}
    
    //This will create a blank module (will run typegen) if not cached
    //Note, this is stored in the generator itself and is not in the namespace
    Module* getModule(Args args);
    

    //This will actually run the generator
    void setModuleDef(Module* m, Args args);
    
    //This will transfer memory management of def to this Generator
    void setDef(GeneratorDef* def) { assert(!this->def); this->def = def;}
    void setGeneratorDefFromFun(ModuleDefGenFun fun);
    Params getGenParams() {return genparams;}

    void setDefaultGenArgs(Args defaultGenfigargs);
    Args getDefaultGenArgs() { return defaultGenArgs;}

};

class Module : public Instantiable {
  Type* type;
  ModuleDef* def = nullptr;
  
  //the directedModule View
  DirectedModule* directedModule = nullptr;
  
  //Memory Management
  vector<ModuleDef*> mdefList;

  public :
    Module(Namespace* ns,string name, Type* type,Params configparams) : Instantiable(IK_Module,ns,name,configparams), type(type) {}
    ~Module();
    static bool classof(const Instantiable* i) {return i->getKind()==IK_Module;}
    bool hasDef() const { return !!def; }
    ModuleDef* getDef() const { return def; } 
    //This will validate def
    void setDef(ModuleDef* def, bool validate=true);
   
    ModuleDef* newModuleDef();
    
    //check for equal graphs, types, genargs, configargs
    //Does not check instance names
    static bool isEqual(Module* m0, Module* m1, bool checkConfig=false, bool checkInstNames=false,bool checkInstantiableNames=false);
    
    DirectedModule* newDirectedModule();
    
    string toString() const;
    json toJson();
    Type* getType() { return type;}
    
    void print(void);
};


// Compiling functions.
// resolve, typecheck, and validate will throw errors (for now)

// This is the resolves the Decls and runs the moduleGens
//void resolve(Context* c, ModuleDef* m);

//Only resolves the Decls
//void resolveDecls(Context* c, ModuleDef* m);

// This verifies that there are no unconnected wires
//void validate(TypedModuleDef* tm);

// This generates verilog
//string verilog(TypedModuleDef* tm);

// Convieniance that runs resolve, typecheck and validate
// and catches errors;
//void compile(Context* c, ModuleDef* m, fstream* f);

}//CoreIR namespace






#endif //INSTANTIABLE_HPP_
