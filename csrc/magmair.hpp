#ifndef MAGMAIR_HPP_
#define MAGMAIR_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include "types.hpp"

using namespace std;

//So much mutual definition, so forward declare
class WireBundleCache;
class WireBundle;
class Interface;
class Instance;
class Select;
class Index;

typedef map<string,string> MetaData ;
typedef std::pair<WireBundle*,WireBundle*> Connection ;

class Circuit {
  protected :
    bool primitive;
    string name;
    MetaData* metadata;
    Type* type;
  public :
    Circuit(bool primitive, string name, Type* type) : primitive(primitive), name(name), type(type) {}
    virtual void print(void)=0;
    string getName(void) {return name;}
    Type* getType(void) {return type;}
};

class Primitive : public Circuit {
  public :
    Primitive(string name, Type* type) : Circuit(true,name,type) {}
    void print(void);
    
};

class Module : public Circuit {
  Interface* interface; 
  vector<Instance*> instances; // Should it be a map?
  vector<Connection> connections;
  WireBundleCache* cache;
  public :
    Module(string name, Type* type);
    ~Module();
    void print(void);
    WireBundleCache* getCache(void);
    Instance* newInstance(string,Circuit*);
    Interface* getInterface(void);
    void newConnect(WireBundle* a, WireBundle* b);
};


class WireBundle {
  protected :
    WireBundleEnum bundleType;
    Module* container; // Module which it is contained in 
    Type* type;
    //TODO should I save head during construction? or figure it out at access
    //WireBundleEnum* head; //Either an interface or an instance
    
    bool _wired; //I am wired
    bool _childrenWired; //at least some downstream children are wired
    vector<WireBundle*> children;
  public :
    WireBundle(WireBundleEnum bundleType, Module* container, Type* type) : bundleType(bundleType),  container(container), type(type), _wired(false) {}
    virtual string _string(void)=0;
    bool isType(WireBundleEnum b) {return bundleType==b;}
    void addChild(WireBundle* wb);
    bool isWired() {return _wired;}
    void setWired();
    virtual void setChildrenWired() {_childrenWired = true;}
    bool hasChildrenWired() {return _childrenWired;}
    void getChildren();
    Select* sel(string);
    Index* idx(uint);
    Module* getContainer(void) { return container;}
    Type* getType(void) { return type;}

};

class Interface : public WireBundle {
  public :
    Interface(Module* container, Type* type) : WireBundle(IFACE,container,type) {}
    string _string();
};

class Instance : public WireBundle {
  string name;
  Circuit* circuitType;
  public :
    Instance(Module* container, Type* type, string name, Circuit* circuitType) : WireBundle(INST,container,type), name(name), circuitType(circuitType) {}
    string _string();
    Circuit* getCircuitType() {return circuitType;}
};

class Select : public WireBundle {
  WireBundle* parent;
  string sel;
  public :
    Select(Module* container, Type* type, WireBundle* parent, string sel);
    string _string();
    void setChildrenWired() {_childrenWired=true; parent->setChildrenWired();}
};

class Index : public WireBundle {
  WireBundle* parent; 
  uint idx;
  public :
    Index(Module* container,Type* type, WireBundle* parent, uint idx);
    string _string();
    void setChildrenWired() {_childrenWired=true; parent->setChildrenWired();}
};

typedef std::tuple<Type*, WireBundle*, string> SelectParamType;
typedef std::tuple<Type*, WireBundle*, uint> IndexParamType;

class WireBundleCache {
  map<SelectParamType,Select*> SelectCache;
  map<IndexParamType,Index*> IndexCache;
  public :
    WireBundleCache() {};
    ~WireBundleCache();
    Select* newSelect(Module* container,Type* type, WireBundle* parent, string sel);
    Index* newIndex(Module* container,Type* type, WireBundle* parent, uint idx);
};

string WireBundleEnum2Str(WireBundleEnum wb);
void Connect(WireBundle* a, WireBundle* b);

Type* getType(Circuit*);

#endif //MAGMAIR_HPP_
