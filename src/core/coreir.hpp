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
#include "enums.hpp"
#include "genargs.hpp"

using namespace std;


//So much mutual definition, so forward declare
class SelCache;
class Wireable;
class Interface;
class Instance;
class Select;


class Instantiable {
  protected:
    InstantiableKind kind;
    string nameSpace;
    string name;
  public :
    Instantiable(InstantiableKind kind, string nameSpace, string name) : kind(kind), nameSpace(nameSpace), name(name) {}
    virtual ~Instantiable() {};
    virtual string toString() const =0;
    string getName() { return name;}
    string getNameSpaceStr() { return nameSpace;}
    string getQualifiedName() { return (nameSpace.empty() ? "this" : nameSpace)  + "." + name; }
    bool isKind(InstantiableKind t) {return kind==t;}
};

std::ostream& operator<<(ostream& os, const Instantiable&);

class GeneratorDecl : public Instantiable {
  
  public :
    
    GeneratorDecl(string nameSpace,string name) : Instantiable(GDEC,nameSpace,name) {}
    virtual ~GeneratorDecl() {}
    string toString() const {
      return "GeneratorDecl: Namespace:"+nameSpace+" name:"+name;
    }

};

class ModuleDef;
class NameSpace;
struct GenArgs;

typedef ModuleDef* (*genfun_t)(NameSpace*,GenArgs*);

class GeneratorDef : public Instantiable {
  genargs_t gentypes;
  genfun_t genfun;
  public :
    GeneratorDef(string name,genargs_t gentypes,genfun_t genfun) : Instantiable(GDEF,"",name), gentypes(gentypes), genfun(genfun) {}
    virtual ~GeneratorDef() {}
    string toString() const {
      return "GeneratorDef: " + name;
    }
    genargs_t getGentypes(void) {return gentypes;}
    genfun_t getGenfun(void) {return genfun;}
};

class ModuleDecl : public Instantiable {
  
  public :
    ModuleDecl(string nameSpace,string name) : Instantiable(MDEC,nameSpace,name) {}
    virtual ~ModuleDecl() {}
    string toString() const {
      return "ModuleDecl: Namespace:"+nameSpace+" name:"+name;
    }
};

typedef std::pair<Wireable*,Wireable*> Wiring ;
class ModuleDef : public Instantiable {
  // TODO move these to 'metadata'
  // TODO think of a better name than 'metadata'
  simfunctions_t sim;
  
  protected:
    Type* type;
    Interface* interface; 
    vector<Instance*> instances; // Should it be a map?
    vector<Wiring> wirings;
    SelCache* cache;

  public :
    string verilog; //TODO
    ModuleDef(string name, Type* type,InstantiableKind e=MDEF);
    virtual ~ModuleDef();
    string toString() const {
      return name;
    }
    Type* getType(void) {return type;}
    SelCache* getCache(void) { return cache;}
    vector<Instance*> getInstances(void) { return instances;}
    vector<Wiring> getWirings(void) { return wirings; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    void addVerilog(string _v) {verilog = _v;}
    void addSimfunctions(simfunctions_t _s) {sim = _s;}

    virtual Instance* addInstance(string,Instantiable*, GenArgs* = nullptr);
    virtual Interface* getInterface(void) {return interface;}
    virtual void wire(Wireable* a, Wireable* b);
    
};


class Wireable;
class Wire {
  protected :
    Wireable* from; // This thing is passive. so it is unused
    vector<Wire*> wirings; 
    Wire* parent;
    map<string,Wire*> children;
  public : 
    Wire(Wireable* from,Wire* parent=nullptr) : from(from), parent(parent) {}
    virtual ~Wire() {}
    virtual string toString() const;
    map<string,Wire*> getChildren() { return children;}
    // TODO will these ever be used?
    Wireable* getFrom() {return from;}
    Wire* getParent() {return parent;}
    
    void addChild(string selStr, Wire* w);
    
    virtual void addWiring(Wire* w);
    
};

class Wireable {
  protected :
    WireableKind kind;
    ModuleDef* container; // ModuleDef which it is contained in 
  public :
    Wire* wire;
    Wireable(WireableKind kind, ModuleDef* container, Wire* wire=nullptr) : kind(kind),  container(container), wire(wire) {}
    ~Wireable() {}
    virtual string toString() const=0;
    ModuleDef* getContainer() { return container;}
    bool isKind(WireableKind e) {
      switch(kind) {
        case IFACE: return e==IFACE;
        case INST: return e==INST;
        case SEL: return e==SEL;
        case TIFACE: return e==TIFACE || e==IFACE;
        case TINST: return e==TINST || e==INST;
        case TSEL: return e==TSEL || e==SEL;
      }
    }
    WireableKind getKind() { return kind ; }
    bool isTyped() { return isKind(TINST) || isKind(TSEL) || isKind(TIFACE); }
    void ptype() {cout << "Type=" <<wireableKind2Str(kind);}
    
    virtual Select* sel(string);
    Select* sel(uint);
    
};

ostream& operator<<(ostream&, const Wireable&);

class Interface : public Wireable {
  public :
    Interface(ModuleDef* container,WireableKind e=IFACE) : Wireable(e,container) { 
      wire = new Wire(this);
    }
    virtual ~Interface() {delete wire;}
    string toString() const;
};

//TODO potentially separate out generator instances and module instances
class Instance : public Wireable {
  string instname;
  Instantiable* instRef;
  
  GenArgs* genargs;
 
  public :
    Instance(ModuleDef* container, string instname, Instantiable* instRef,GenArgs* genargs =nullptr, WireableKind e=INST) : Wireable(e,container), instname(instname), instRef(instRef), genargs(genargs) {
      wire = new Wire(this);
    }
    virtual ~Instance() {if(genargs) delete genargs; delete wire;}
    string toString() const;
    Instantiable* getInstRef() {return instRef;}
    string getInstname() { return instname; }
    GenArgs* getGenArgs() {return genargs;}
    void replace(Instantiable* newRef) { instRef = newRef;}
};

class Select : public  Wireable {
  protected :
    Wireable* parent;
    string selStr;
  public :
    Select(ModuleDef* container, Wireable* parent, string selStr, WireableKind e=SEL) : Wireable(e,container), parent(parent), selStr(selStr) {
      //TODO hack
      if (e==SEL) {
        wire = new Wire(this);
        parent->wire->addChild(selStr,wire);
      }
    }
    virtual ~Select() {delete wire;}
    string toString() const;
    Wireable* getParent() { return parent; }
    string getSelStr() { return selStr; }
};


class TypedSelect;
typedef std::pair<Wireable*, string> SelectParamType;
class SelCache {
  map<SelectParamType,Select*> cache;
  map<SelectParamType,TypedSelect*> typedcache;
  public :
    SelCache() {};
    ~SelCache();
    Select* newSelect(ModuleDef* container, Wireable* parent, string selStr);
    TypedSelect* newTypedSelect(ModuleDef* container, Wireable* parent, Type* type, string selStr);
};


class CoreIRContext;
class NameSpace;


class NameSpace {
  string nameSpace;
  map<string,ModuleDef*> modList;
  map<string,GeneratorDef*> genList;
  public :
    NameSpace(string nameSpace) : nameSpace(nameSpace) {}
    ~NameSpace();
    string getName() { return nameSpace;}
    
    ModuleDef* moduleDefLookup(string name);
    GeneratorDef* generatorDefLookup(string name);
    
    // Note: These will take control over managing the pointers
    void addModuleDef(ModuleDef* m);
    void addGeneratorDef(GeneratorDef* g);
    
    void print() {
      cout << "NameSpace: " << nameSpace << endl;
      cout << "  ModuleDefs:" << endl;
      for (auto it : modList) cout << "    " << it.second->toString() <<endl;
      cout << "  GeneratorDefs:" << endl;
      for (auto it : genList) cout << "    " << it.second->toString() <<endl;
      cout << endl;
    }

};



class CoreIRContext {
  NameSpace* global;
  map<string,NameSpace*> libs;
  vector<Instantiable*> opaques;
  public :
    CoreIRContext();
    ~CoreIRContext();
    NameSpace* getGlobal() {return global;}
    NameSpace* registerLib(string name);
    NameSpace* nameSpaceLookup(string name);
    ModuleDecl* declareMod(string nameSpace, string name);
    GeneratorDecl* declareGen(string nameSpace,string name);
};

CoreIRContext* newContext();
void deleteContext(CoreIRContext* m);




/////

// Int Type functions
IntType* Int(uint bits, Dir dir);
IntType* Int(uint bits);
//Type* Float(uint ebits, uint mbits, Dir dir);
//Type* Bool(Dir dir);
ArrayType* Array(Type* elemType, uint len);
RecordType* Record(recordparam_t record);
Type* Sel(Type* record, string key);
Type* Flip(Type*);
Type* In(Type*);
Type* Out(Type*);

typedef struct dirty_t {
  uint8_t dirty;
} dirty_t;

uint8_t isDirty(dirty_t* d);
void setDirty(dirty_t* d);

void* allocateFromType(Type* t);
void deallocateFromType(Type* t, void* d);

class TypedModuleDef;

// Compiling functions.
// resolve, typecheck, and validate will throw errors (for now)

// This is the linker that resolves the Decl and runs the generators
// For now resolve mutates m to change every instantiable to a ModuleDef
void resolve(CoreIRContext* c, ModuleDef* m);
  
// This 'typechecks' everything
  //   Verifies all selects are valid
  //   Verifies all connections are valid. type <==> FLIP(type)
  //   Verifies inputs are only connected once

typedef map<ModuleDef*,TypedModuleDef*> typechecked_t;
typechecked_t* typecheck(CoreIRContext* c, ModuleDef* m);

// This generates verilog
string verilog(TypedModuleDef* tm);

// This verifies that there are no unconnected wires
void validate(TypedModuleDef* tm);

// Convieniance that runs resolve, typecheck and validate
// and catches errors;
void compile(CoreIRContext* c, ModuleDef* m, fstream* f);



#endif //COREIR_HPP_
