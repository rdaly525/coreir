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


class Module {
  string name;
  bool terminal;
  MetaData* metadata;
  Type* type;
  Interface* interface; 
  vector<Instance*> instances; // Should it be a map?
  vector<Connection> connections;
  WireBundleCache* cache;
  public :
    Module(string name, bool terminal, Type* type);
    ~Module();
    void print(void);
    WireBundleCache* getCache(void);
    string getName(void) { return name;}
    Instance* newInstance(string,Module*);
    Interface* getInterface(void);
    Type* getType(void) {return type;}
    void newConnect(WireBundle* a, WireBundle* b);
};


class WireBundle {
  protected :
    WireBundleEnum bundleType;
    Module* container; // Module which it is contained in 
    Type* type;
  //TODO should I save head during construction? or figure it out at access
  //WireBundleEnum* head; //Either an interface or an instance
  public :
    WireBundle(WireBundleEnum bundleType, Module* container, Type* type) : bundleType(bundleType),  container(container), type(type) {}
    virtual string _string(void)=0;
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
  Module* modType;
  public :
    Instance(Module* container, Type* type, string name, Module* modType) : WireBundle(INST,container,type), name(name), modType(modType) {}
    string _string();
};

class Select : public WireBundle {
  WireBundle* parent;
  string sel;
  public :
    Select(Module* container, Type* type, WireBundle* parent, string sel) : WireBundle(SEL,container,type), parent(parent), sel(sel) {}
    string _string();

};

class Index : public WireBundle {
  WireBundle* parent; 
  uint idx;
  public :
    Index(Module* container,Type* type, WireBundle* parent, uint idx) : WireBundle(IDX,container,type), parent(parent), idx(idx) {}
    string _string();
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

#endif //MAGMAIR_HPP_
