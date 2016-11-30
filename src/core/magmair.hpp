#ifndef MAGMAIR_HPP_
#define MAGMAIR_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <cassert>
#include "types.hpp"


using namespace std;






//So much mutual definition, so forward declare
class WireableCache;
class Wireable;
class Interface;
class Instance;
class Select;

typedef map<string,string> MetaData ;
typedef std::pair<Wireable*,Wireable*> Connection ;

class Circuit {
  protected :
    bool _primitive;
    bool _mutable;
    string name;
    MetaData* metadata;
    Type* type;
  public :
    Circuit(bool _primitive, string name, Type* type) : _primitive(_primitive), _mutable(true), name(name), type(type) {}
    virtual ~Circuit() {}
    virtual void print(void)=0;
    string getName(void) {return name;}
    Type* getType(void) {return type;}
    bool isPrimitive() { return _primitive;}
    void makeImmutable() { _mutable = false;}
    bool isMutable() { return _mutable;}
};

class Primitive : public Circuit {
  public :
    Primitive(string name, Type* type) : Circuit(true,name,type) {}
    ~Primitive() {}
    void print(void);
};

class Module : public Circuit {
  Interface* interface; 
  vector<Instance*> instances; // Should it be a map?
  vector<Connection> connections;
  
  WireableCache* cache;
  public :
    Module(string name, Type* type);
    ~Module();
    void print(void);
    WireableCache* getCache(void);
    Instance* newInstance(string,Circuit*);
    Interface* getInterface(void);
    vector<Instance*> getInstances(void) { return instances;}
    vector<Connection> getConnections(void) { return connections; }
    void newConnect(Wireable* a, Wireable* b);
};

//TODO Maybe change children to be a record or array. This would let me check if everything is wired

class Wireable {
  protected :
    WireableEnum bundleType;
    Module* container; // Module which it is contained in 
    Type* type;
    //TODO should I save head during construction? or figure it out at access
    //WireableEnum* head; //Either an interface or an instance (or Constant?)
    
    bool _parentWired; // a parent is either _wired or _parentWired
    bool _wired; //I am wired (entirely). Implies connections contains at least one
    bool _childrenWired; //some children *inputs* are wired

    vector<Wireable*> connections; 
    map<string,Wireable*> children;
  public :
    Wireable(WireableEnum bundleType, Module* container, Type* type) : bundleType(bundleType),  container(container), type(type), _parentWired(false), _wired(false), _childrenWired(false) {}
    virtual ~Wireable() {}
    virtual string _string(void)=0;
    bool isType(WireableEnum b) {return bundleType==b;}
    WireableEnum getBundleType() { return bundleType; }
    void addChild(string sel,Wireable* wb);
    bool isParentWired() { return _parentWired;}
    bool isWired() {return _wired;}
    bool hasChildrenWired() {return _childrenWired;}
    void setParentWired(); //Set _parentWired and all children's setParentWired
    void addConnection(Wireable* w); //Set _wired and all children's setParentWired
    virtual void setChildrenWired() {_childrenWired = true;}
    bool checkWired(); //recursively checks if wired
    Select* sel(string);
    Select* sel(uint);
    Module* getContainer(void) { return container;}
    Type* getType(void) { return type;}

};

class Interface : public Wireable {
  public :
    Interface(Module* container, Type* type) : Wireable(IFACE,container,type) {}
    ~Interface() {}
    string _string();
};

class Instance : public Wireable {
  string name;
  Circuit* circuitType;
  public :
    Instance(Module* container, Type* type, string name, Circuit* circuitType) : Wireable(INST,container,type), name(name), circuitType(circuitType) {}
    ~Instance() {}
    string _string();
    Circuit* getCircuitType() {return circuitType;}
    string getName() { return name; }
    void replace(Circuit* c) {circuitType = c;} //TODO dangerous. Could point to its container.
};

class Select : public Wireable {
  Wireable* parent;
  string selStr;
  public :
    Select(Module* container, Type* type, Wireable* parent, string selStr);
    ~Select() {}
    string _string();
    void setChildrenWired() {_childrenWired=true; parent->setChildrenWired();}
    Wireable* getParent() { return parent; }
    string getSelStr() { return selStr; }
};

typedef std::tuple<Type*, Wireable*, string> SelectParamType;

class WireableCache {
  map<SelectParamType,Select*> SelectCache;
  public :
    WireableCache() {};
    ~WireableCache();
    Select* newSelect(Module* container,Type* type, Wireable* parent, string sel);
};


//TODO should I move the typeCache into MagmaIR? 
//means that I have to pass the magmaIR object in to type constructors
class MagmaIR {
  public :
    vector<Primitive*> primList;
    vector<Module*> modList;
    MagmaIR() {}
    ~MagmaIR() { 
      for(vector<Primitive*>::iterator it=primList.begin(); it!=primList.end(); ++it) delete (*it);
      for(vector<Module*>::iterator it=modList.begin(); it!=modList.end(); ++it) delete (*it);
    }
    Module* newModule(string name, Type* type);
    Primitive* newPrimitive(string name, Type* type);
};

MagmaIR* newMagmaIR();
void deleteMagmaIR(MagmaIR* m);


string WireableEnum2Str(WireableEnum wb);
void Connect(Wireable* a, Wireable* b);


Type* getType(Circuit*);
bool Validate(Circuit* c);



// Int Type functions
IntType* Int(uint bits, Dir dir);
IntType* Int(uint bits);
//Type* Float(uint ebits, uint mbits, Dir dir);
//Type* Bool(Dir dir);
ArrayType* Array(Type* elemType, uint len);
RecordType* Record(map<string,Type*> record);
RecordType* AddField(RecordType* record, string key, Type* val);
Type* Sel(Type* record, string key);
Type* Flip(Type*);




#endif //MAGMAIR_HPP_
