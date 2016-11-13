#ifndef MAGMAIR_HPP_
#define MAGMAIR_HPP_


#include <iostream>
#include <string>
#include <map>
using namespace std;

typedef MetaData map<string,string>;
typedef WireInstr std::pair<WireBundle*,WireBundle*>
class Module {
  string name;
  MetaData* metadata;
  Type* type;
  Interface* interface; 
  Vector<Instance*> instances; // Should it be a map?
  Vector<WireInstr> wireinstrs;
  public :
    module(string name, MetaData* metadata, Type* type) : name(name), metadata(metadata), type(type) {
      interface = new Interface(flip(type),this)
    }
    
    string _string(void);
    void print(void);
    Instance* newInstance(string,Module*);
    Interface* getInterface(void);
};

typedef enum {IFACE,INST,SEL,IDX} WireBundleType

class WireBundle {
  WireBundleType bundleType;
  Type* type;
  public :
    WireBundle(Type* typeWireBundleType, bundleType) : type(type), bundleType(bundleType) {}
    Select* Select(string);
    Index* Index(uint);
};

class Interface : public WireBundle {
  Module* mod;
  public :
    Interface(Type* type, Module* mod) : WireBundle(type,IFACE), mod(mod) {}
}
class Instance : public WireBundle {
  Module* moduleType;
  public :
    Instance(Type* type, Module* modType) : WireBundle(type,INST), modType(modType) {}
};

class Select : public WireBundle {
  WireBundle* fromwire;
  string sel;
  public :
    Select(Type* type, WireBundle* fromwire, string fromsel) : WireBundle(type,SEL), fromwire(fromwire), sel(sel) {}

};

class Index : public WireBundle {
  WireBundle* fromwire;
  uint idx;
  public :
    Index(Type* type, Wirebundle* fromwire, uint idx) : WireBundle(type,IDX), fromwire(fromwire), fromsel(fromsel) {}
}

void Connect(WireBundle* a, WireBundle* b);

#endif //MAGMAIR_HPP_
