#ifndef WIREABLE_HPP_
#define WIREABLE_HPP_

#include "metadata.hpp"
#include "moduledef.hpp"

using namespace std;

namespace CoreIR {

class Wireable {
  public:
    enum WireableKind {WK_Interface,WK_Instance,WK_Select};

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
    unordered_map<string,Wireable*> getSelects() { return selects;}
    bool hasSel(string selstr) {return selects.count(selstr) >0;}
    Metadata getMetadata() { return metadata;}
    ModuleDef* getModuleDef() { return moduledef;}
    Context* getContext();
    WireableKind getKind() const { return kind; }
    Type* getType() { return type;}
    void addConnectedWireable(Wireable* w) { connected.insert(w); }
    void removeConnectedWireable(Wireable* w) {
      assert(connected.count(w) > 0);
      connected.erase(w);
    }
    
    Select* sel(string);
    Select* sel(uint);
    Select* sel(SelectPath);
  
    // if this wireable is from add3inst.a.b[0], then this will look like
    // {add3inst,a,b,0}
    SelectPath getSelectPath();
    ConstSelectPath getConstSelectPath();
    string wireableKind2Str(WireableKind wb);
    LocalConnections getLocalConnections();
    Wireable* getTopParent();
};

ostream& operator<<(ostream&, const Wireable&);

class Interface : public Wireable {
  static const string instname;
  public :
    Interface(ModuleDef* context,Type* type) : Wireable(WK_Interface,context,type) {};
    static bool classof(const Wireable* w) {return w->getKind()==WK_Interface;}
    string toString() const;
    const string& getInstname() { return instname; }
};

class Instance : public Wireable {
  const string instname;
  Module* moduleRef;
  
  Args configargs;
  
  bool isgen;
  Generator* generatorRef = nullptr;
  Args genargs;
  
  public :
    Instance(ModuleDef* context, string instname, Module* moduleRef, Args configargs=Args());
    Instance(ModuleDef* context, string instname, Generator* generatorRef, Args genargs, Args configargs=Args());
    static bool classof(const Wireable* w) {return w->getKind()==WK_Instance;}
    string toString() const;
    json toJson();
    Module* getModuleRef() {return moduleRef;}
    const string& getInstname() { return instname; }
    Arg* getConfigArg(string s);
    Args getConfigArgs() const {return configargs;}
    bool hasConfigArgs() {return !configargs.empty();}
    
    //Convinience functions
    bool isGen() { return isgen;}
    Generator* getGeneratorRef() { return generatorRef;}
    Instantiable* getInstantiableRef();
    Args getGenArgs() {return genargs;}
    
    void runGenerator();
    void replace(Module* moduleRef, Args configargs=Args());
    void replace(Generator* generatorRef, Args genargs, Args configargs=Args());
};

class Select : public Wireable {
  protected :
    Wireable* parent;
    string selStr;
  public :
    Select(ModuleDef* context, Wireable* parent, string selStr, Type* type) : Wireable(WK_Select,context,type), parent(parent), selStr(selStr) {}
    static bool classof(const Wireable* w) {return w->getKind()==WK_Select;}
    string toString() const;
    Wireable* getParent() { return parent; }
    const string& getSelStr() { return selStr; }
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
