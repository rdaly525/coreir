#ifndef COREIR_HPP_
#define COREIR_HPP_


#include <iostream>
#include <string>
#include <map>
#include <set>
#include <vector>
#include <cassert>
#include "types.hpp"
#include "enums.hpp"

using namespace std;


//So much mutual definition, so forward declare
class WireableCache;
class Wireable;
class Interface;
class Instance;
class Select;


class Instantiable {
  protected:
    InstantiableEnum instantiableType;
    string nameSpace;
    string name;
  public :
    Instantiable(InstantiableEnum instantiableType, string nameSpace, string name) : instantiableType(instantiableType), nameSpace(nameSpace), name(name) {}
    virtual ~Instantiable() {};
    bool isType(InstantiableEnum t) {return instantiableType==t;}
    string getName() { return name;}
    string getNameSpaceStr() { return nameSpace;}
    virtual string toString() const =0;
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
struct Genargs;

typedef ModuleDef* (*genfun_t)(NameSpace*,Genargs*);

class GeneratorDef : public Instantiable {
  genfun_t genfun;
  public :
    GeneratorDef(string name,genfun_t genfun) : Instantiable(GDEF,"",name), genfun(genfun) {}
    virtual ~GeneratorDef() {}
    genfun_t getGenfun(void) {return genfun;}
    string toString() const {
      return "GeneratorDef: " + name;
    }
};

class ModuleDecl : public Instantiable {
  
  public :
    ModuleDecl(string nameSpace,string name) : Instantiable(MDEC,nameSpace,name) {}
    virtual ~ModuleDecl() {}
    string toString() const {
      return "ModuleDecl: Namespace:"+nameSpace+" name:"+name;
    }
};

struct simfunctions_t {
  //void* iface,void* state,void* dirty,void* genargs)
  void (*updateOutput)(void*,void*,void*,Genargs*);
  void* (*allocateState)(void);
  void (*updateState)(void*,void*,void*,Genargs*);
  void (*deallocateState)(void*);
};

typedef std::pair<Wireable*,Wireable*> Wiring ;

// TODO change this to support modules and whatever else is needed
struct Genargs {
  Type* type;
  void* data;
  Genargs(Type* type);
  ~Genargs();

};


class NameSpace;
class ModuleDef : public Instantiable {
  Type* type;
  Interface* interface; 
  vector<Instance*> instances; // Should it be a map?
  vector<Wiring> wirings;
  WireableCache* cache;
  
  // TODO move these to 'metadata'
  // TDOO think of a better name than 'metadata'
  string verilog;
  simfunctions_t sim;

  public :
    ModuleDef(string name, Type* type);
    virtual ~ModuleDef();
    void print(void);
    void addVerilog(string _v) {verilog = _v;}
    void addSimfunctions(simfunctions_t _s) {sim = _s;}

    // User has control over Genargs
    Instance* addInstance(string,Instantiable*, Genargs* = nullptr);
    Interface* getInterface(void) {return interface;}
    void wire(Wireable* a, Wireable* b);
    
    WireableCache* getCache(void) { return cache;}
    vector<Instance*> getInstances(void) { return instances;}
    vector<Wiring> getWirings(void) { return wirings; }
    string toString() const {
      return name;
    }
};



class Wireable {
  protected :
    WireableEnum wireableType;
    ModuleDef* container; // ModuleDef which it is contained in 
    vector<Wireable*> wirings; 
    map<string,Wireable*> children;
  public : 
    Wireable(WireableEnum wireableType, ModuleDef* container) : wireableType(wireableType),  container(container) {}
    ~Wireable() {}
    ModuleDef* getContainer() { return container;}
    void addChild(string selStr, Wireable* wb);
    void addWiring(Wireable* w);
    Select* sel(string);
    Select* sel(uint);
    virtual string toString() const=0;
};

ostream& operator<<(ostream&, const Wireable&);

class Interface : public Wireable {
  public :
    Interface(ModuleDef* container) : Wireable(IFACE,container) {}
    virtual ~Interface() {}
    string toString() const;
};

class Select : public Wireable {
  Wireable* parent;
  string selStr;
  public :
    Select(ModuleDef* container, Wireable* parent, string selStr) : Wireable(SEL,container), parent(parent), selStr(selStr) {}
    virtual ~Select() {}
    Wireable* getParent() { return parent; }
    string getSelStr() { return selStr; }
    string toString() const;
};

//TODO potentially separate out generator instances and module instances
class Instance : public Wireable {
  string name;
  Instantiable* instRef;
  
  Genargs* genargs;
 
  public :
    Instance(ModuleDef* container, string name, Instantiable* instRef,Genargs* genargs =nullptr) : Wireable(INST,container), name(name), instRef(instRef), genargs(genargs) {}
    virtual ~Instance() {if(genargs) delete genargs;}
    void replace(Instantiable* newRef) { instRef = newRef;}
    Instantiable* getInstRef() {return instRef;}
    string getName() { return name; }
    Genargs* getGenargs() {return genargs;}
    string toString() const;
};

typedef std::pair<Wireable*, string> SelectParamType;
class WireableCache {
  map<SelectParamType,Select*> SelectCache;
  public :
    WireableCache() {};
    ~WireableCache();
    Select* newSelect(ModuleDef* container, Wireable* parent, string sel);
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
string WireableEnum2Str(WireableEnum wb);
bool Validate(Instantiable* c);

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

void compile2Verilog(ModuleDef* m);

typedef struct dirty_t {
  uint8_t dirty;
} dirty_t;

uint8_t isDirty(dirty_t* d);
void setDirty(dirty_t* d);

void* allocateFromType(Type* t);
void deallocateFromType(Type* t, void* d);

void compile(CoreIRContext* c, ModuleDef* m);
void resolve(CoreIRContext* c, ModuleDef* m, set<ModuleDef*>* resolvedMods);

#endif //COREIR_HPP_
