#ifndef COREIR_HPP_
#define COREIR_HPP_


#include <fstream>
#include <iostream>
#include <string>
#include <map>
#include <set>
#include <vector>
#include <cassert>

#include "types.hpp"
#include "common.hpp"
#include "genargs.hpp"

using namespace std;


//So much mutual definition, so forward declare
class SelCache;
class Wireable;
class Interface;
class Instance;
class Select;


class Context;
class Instantiable {
  protected:
    InstantiableKind kind;
    Namespace* ns;
    string name;
  public :
    Instantiable(InstantiableKind kind, Namespace* ns, string name) : kind(kind), ns(ns), name(name) {}
    virtual ~Instantiable() {};
    virtual bool hasDef() const=0;
    virtual string toString() const =0;
    bool isKind(InstantiableKind k) const { return kind==k;}
    InstantiableKind getKind() const { return kind;}
    Module* toModule();
    Generator* toGenerator();
    Context* getContext();
    string getName() const { return name;}
    Namespace* getNamespace() const { return ns;}
    friend bool operator==(const Instantiable & l,const Instantiable & r);
};

std::ostream& operator<<(ostream& os, const Instantiable&);


class Generator : public Instantiable {
  ArgKinds argkinds;
  TypeGen* typegen;
  genFun genfun;
  public :
    Generator(Namespace* ns,string name,ArgKinds argkinds, TypeGen* typegen);
    bool hasDef() const { return !!genfun; }
    string toString() const;
    TypeGen* getTypeGen() { return typegen;}
    genFun getDef() { return genfun;}
    void addDef(genFun fun) { genfun = fun;}
    //genargs_t getGentypes(void) {return gentypes;}
    //genfun_t getGenfun(void) {return genfun;}
};

class Module : public Instantiable {
  Type* type;
  ModuleDef* def;
  string verilog;
  
  //Memory Management
  vector<ModuleDef*> mdefList;

  public :
    Module(Namespace* ns,string name, Type* type) : Instantiable(MOD,ns,name), type(type), def(nullptr) {}
    ~Module();
    bool hasDef() const { return !!def; }
    ModuleDef* getDef() { return def; } // TODO should probably throw error if does not exist
    string toString() const;
    Type* getType() { return type;}
    void addDef(ModuleDef* _def) { assert(!def); def = _def;}
    void replaceDef(ModuleDef* _def) { def = _def;}
    ModuleDef* newModuleDef();
    void print(void);
    //TODO turn this into metadata
    void addVerilog(string _v) {verilog = _v;}
};

typedef std::pair<Wireable*,Wireable*> Wiring ;
class ModuleDef {
  
  protected:
    Module* module;
    Interface* interface; 
    map<string,Instance*> instances;
    set<Wiring> wires;
    SelCache* cache;

  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    //SelCache* getCache(void) { return cache;}
    map<string,Instance*> getInstances(void) { return instances;}
    set<Wiring> getWires(void) { return wires; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    Context* getContext() { return module->getContext(); }
    string getName() {return module->getName();}
    Type* getType() {return module->getType();}
    SelCache* getCache() { return cache;}
    Instance* addInstanceGenerator(string,Generator*, GenArgs*);
    Instance* addInstanceModule(string,Module*);
    Instance* addInstance(Instance* i); //copys info about i
    Interface* getInterface(void) {return interface;}
    Wireable* sel(string s);
    void wire(Wireable* a, Wireable* b);
    
};

class Wireable {
  protected :
    WireableKind kind;
    ModuleDef* moduledef; // ModuleDef which it is contained in 
    Type* type;
    set<Wireable*> wirings; 
    map<string,Wireable*> children;
  public :
    Wireable(WireableKind kind, ModuleDef* moduledef, Type* type) : kind(kind),  moduledef(moduledef), type(type) {}
    virtual ~Wireable() {}
    virtual string toString() const=0;
    set<Wireable*> getWires() { return wirings;}
    map<string,Wireable*> getChildren() { return children;}
    ModuleDef* getModuleDef() { return moduledef;}
    Context* getContext() { return moduledef->getContext();}
    bool isKind(WireableKind e) { return e==kind;}
    WireableKind getKind() { return kind ; }
    Type* getType() { return type;}
    void ptype() {cout << "Kind=" <<wireableKind2Str(kind);}
    void addWiring(Wireable* w) { wirings.insert(w); }
    
    Select* sel(string);
    Select* sel(uint);
  
    // Convinience function
    // if this wireable is from add3inst.a.b[0], then this will look like
    // {add3inst,{a,b,0}}
    std::pair<string,vector<string>> getPath();

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
  
  GenArgs* genargs;
 
  public :
    Instance(ModuleDef* context, string instname, Instantiable* instRef,Type* type, GenArgs* genargs =nullptr)  : Wireable(INST,context,type), instname(instname), instRef(instRef), genargs(genargs) {}
    string toString() const;
    Instantiable* getInstRef() {return instRef;}
    string getInstname() { return instname; }
    GenArgs* getGenArgs() {return genargs;}
    //void replace(Instantiable* newRef) { instRef = newRef;}
    //Convinience functions
    bool isGen() { return instRef->isKind(GEN);}
    bool hasDef() { return instRef->hasDef(); }
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

#endif //COREIR_HPP_
