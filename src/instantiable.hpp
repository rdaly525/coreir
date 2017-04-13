#ifndef COREIR_HPP_
#define COREIR_HPP_


#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cassert>

#include "common.hpp"
#include "context.hpp"
#include "types.hpp"
#include "args.hpp"
#include "json.hpp"
#include "metadata.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {

class Instantiable {
  protected:
    InstantiableKind kind;
    Namespace* ns;
    string name;
    Metadata metadata;
    Params configparams;
  public :
    Instantiable(InstantiableKind kind, Namespace* ns, string name, Params configparams) : kind(kind), ns(ns), name(name), configparams(configparams) {}
    virtual ~Instantiable() {}
    virtual bool hasDef() const=0;
    virtual string toString() const =0;
    bool isKind(InstantiableKind k) const { return kind==k;}
    InstantiableKind getKind() const { return kind;}
    Module* toModule();
    Generator* toGenerator();
    Context* getContext();
    Params getConfigParams() { return configparams;}
    Metadata getMetadata() { return metadata;}
    string getName() const { return name;}
    virtual json toJson()=0;
    Namespace* getNamespace() const { return ns;}
    friend bool operator==(const Instantiable & l,const Instantiable & r);
};

std::ostream& operator<<(ostream& os, const Instantiable&);


class Generator : public Instantiable {
  Params genparams;
  TypeGen typegen;
  ModuleDefGenFun genfun;
  public :
    Generator(Namespace* ns,string name,Params genparams, TypeGen typegen, Params configparams=Params());
    bool hasDef() const { return !!genfun; }
    string toString() const;
    json toJson();
    TypeGen getTypeGen() { return typegen;}
    ModuleDefGenFun getDef() { return genfun;}
    void addDef(ModuleDefGenFun fun) { genfun = fun;}
    Params getGenparams() {return genparams;}
};

class Module : public Instantiable {
  Type* type;
  ModuleDef* def;
  string verilog;
  
  //Memory Management
  vector<ModuleDef*> mdefList;

  public :
    Module(Namespace* ns,string name, Type* type,Params configparams) : Instantiable(MOD,ns,name,configparams), type(type), def(nullptr) {}
    ~Module();
    bool hasDef() const { return !!def; }
    ModuleDef* getDef() { return def; } // TODO should probably throw error if does not exist
    string toString() const;
    json toJson();
    Type* getType() { return type;}
    void addDef(ModuleDef* _def) { assert(!def); def = _def;}
    void replaceDef(ModuleDef* _def) { def = _def;}
    ModuleDef* newModuleDef();
    void print(void);
    //TODO turn this into metadata
    void addVerilog(string _v) {verilog = _v;}
};

class ModuleDef {
  
  protected:
    Module* module;
    Interface* interface; 
    unordered_map<string,Instance*> instances;
    unordered_set<Connection*> connections;
    SelCache* cache;
    Metadata metadata;
    Metadata implementations; // TODO maybe have this just be inhereted moduledef classes

  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    //SelCache* getCache(void) { return cache;}
    unordered_map<string,Instance*> getInstances(void) { return instances;}
    unordered_set<Connection*> getConnections(void) { return connections; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    Context* getContext() { return module->getContext(); }
    string getName() {return module->getName();}
    Type* getType() {return module->getType();}
    SelCache* getCache() { return cache;}
    Metadata getMetadata() { return metadata;}
    Module* getModule() { return module; }
    Instance* addInstance(string,Generator*,Args genargs, Args config=Args());
    Instance* addInstance(string,Module*,Args config=Args());
    Instance* addInstance(Instance* i); //copys info about i
    Interface* getInterface(void) {return interface;}
    Wireable* sel(string s);
    void wire(Wireable* a, Wireable* b);
    void wire(WirePath a, WirePath b);
    json toJson();
    
};

class Wireable {
  protected :
    WireableKind kind;
    ModuleDef* moduledef; // ModuleDef which it is contained in 
    Type* type;
    unordered_set<Wireable*> connected; 
    unordered_map<string,Wireable*> selects;
    Metadata metadata;
  public :
    Wireable(WireableKind kind, ModuleDef* moduledef, Type* type) : kind(kind),  moduledef(moduledef), type(type) {}
    virtual ~Wireable() {}
    virtual string toString() const=0;
    unordered_set<Wireable*> getConnectedWireables() { return connected;}
    unordered_map<string,Wireable*> getChildren() { return selects;}
    Metadata getMetadata() { return metadata;}
    ModuleDef* getModuleDef() { return moduledef;}
    Context* getContext() { return moduledef->getContext();}
    bool isKind(WireableKind e) { return e==kind;}
    WireableKind getKind() { return kind; }
    Type* getType() { return type;}
    void addConnectedWireable(Wireable* w) { connected.insert(w); }
    
    Select* sel(string);
    Select* sel(uint);
  
    // Convinience function
    // if this wireable is from add3inst.a.b[0], then this will look like
    // {add3inst,{a,b,0}}
    WirePath getPath();

};

ostream& operator<<(ostream&, const Wireable&);

class Interface : public Wireable {
  public :
    Interface(ModuleDef* context,Type* type) : Wireable(IFACE,context,type) {};
    string toString() const;
};

//TODO potentially separate out moduleGen instances and module instances
class Instance : public Wireable {
  string instname;
  Instantiable* instRef;
  Args genargs;
  Args config;
  
  public :
    Instance(ModuleDef* context, string instname, Instantiable* instRef,Type* type, Args genargs, Args config)  : Wireable(INST,context,type), instname(instname), instRef(instRef),genargs(genargs), config(config) {}
    string toString() const;
    json toJson();
    Instantiable* getInstRef() {return instRef;}
    string getInstname() { return instname; }
    Arg* getConfigValue(string s);
    Args getArgs() {return genargs;}
    Args getConfig() {return config;}
    bool hasConfig() {return !config.empty();}
    //void replace(Instantiable* newRef) { instRef = newRef;}
    //Convinience functions
    bool isGen() { return instRef->isKind(GEN);}
    bool hasDef() { return instRef->hasDef(); }
    void replace(Instantiable* _instRef, Args _config) {
      this->instRef = _instRef;
      this->config = _config;
    }
};

class Select : public Wireable {
  protected :
    Wireable* parent;
    string selStr;
  public :
    Select(ModuleDef* context, Wireable* parent, string selStr, Type* type) : Wireable(SEL,context,type), parent(parent), selStr(selStr) {}
    string toString() const;
    Wireable* getParent() { return parent; }
    string getSelStr() { return selStr; }
};


typedef std::pair<Wireable*, string> SelectParamType;
class SelCache {
  map<SelectParamType,Select*> cache;
  public :
    SelCache() {};
    ~SelCache();
    Select* newSelect(ModuleDef* context, Wireable* parent, string selStr,Type* t);
};


//void* allocateFromType(Type* t);
//void deallocateFromType(Type* t, void* d);


// Compiling functions.
// resolve, typecheck, and validate will throw errors (for now)

// For now, these functions mutate m. TODO (bad compiler practice probably)

// This is the resolves the Decls and runs the moduleGens
void resolve(Context* c, ModuleDef* m);

//Only resolves the Decls
void resolveDecls(Context* c, ModuleDef* m);

//Only runs the moduleGens
void runGenerators(Context* c, ModuleDef* m);


// This 'typechecks' everything
  //   Verifies all selects are valid
  //   Verifies all connections are valid. type <==> FLIP(type)
  //   Verifies inputs are only connected once

//typedef map<ModuleDef*,TypedModuleDef*> typechecked_t;
//typechecked_t* typecheck(Context* c, ModuleDef* m);


// This verifies that there are no unconnected wires
//void validate(TypedModuleDef* tm);

// This generates verilog
//string verilog(TypedModuleDef* tm);

// Convieniance that runs resolve, typecheck and validate
// and catches errors;
void compile(Context* c, ModuleDef* m, fstream* f);

}//CoreIR namespace






#endif //COREIR_HPP_
