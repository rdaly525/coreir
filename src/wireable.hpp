#ifndef WIREABLE_HPP_
#define WIREABLE_HPP_

#include "metadata.hpp"
#include "moduledef.hpp"

using namespace std;

namespace CoreIR {

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
    Context* getContext();
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

class Instance : public Wireable {
  string instname;
  Module* moduleRef;
  
  Args configargs;
  
  bool isgen;
  Generator* generatorRef;
  Args genargs;
  
  public :
    Instance(ModuleDef* context, string instname, Module* moduleRef, Args configargs=Args());
    Instance(ModuleDef* context, string instname, Generator* generatorRef, Args genargs, Args configargs=Args());
    string toString() const;
    json toJson();
    Module* getModuleRef() {return moduleRef;}
    string getInstname() { return instname; }
    Arg* getConfigArg(string s);
    Args getConfigArgs() {return configargs;}
    bool hasConfigArgs() {return !configargs.empty();}
    
    //Convinience functions
    bool isGen() { return isgen;}
    Generator* getGeneratorRef() { return generatorRef;}
    Args getGenargs() {return genargs;}
    void runGenerator();
    //void replace(Instantiable* instRef, Args config);
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


}//CoreIR namespace

#endif //WIREABLE_HPP_
