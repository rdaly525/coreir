#include <iostream>
#include <string>
#include <map>
using namespace std;

typedef MetaData map<string,string>;
typedef WireInstr std::pair<Wire*,Wire*>
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

class WireBundle {
  Type* type;
  public :
    WireBundle(Type* type) : type(type) {}
    Select* Select(string);
    Index* Index(uint);
};

class Interface : public WireBundle {
  Module* mod;
  public :
    Interface(Type* type, Module* mod) : WireBundle(type), mod(mod) {}
}
class Instance : public WireBundle {
  Module* moduleType;
  public :
    Instance(Type* type, Module* modType) : WireBundle(type), modType(modType) {}
};

class Select : public WireBundle {
  WireBundle* fromwire;
  string sel;
  public :
    Select(Type* type, WireBundle* fromwire, string fromsel) : WireBundle(type), fromwire(fromwire), sel(sel) {}

};

class Index : public WireBundle {
  WireBundle* fromwire;
  uint idx;
  public :
    Index(Type* type, Wirebundle* fromwire, uint idx) : WireBundle(type), fromwire(fromwire), fromsel(fromsel) {}
}

void Connect(WireBundle* a, WireBundle* b)

