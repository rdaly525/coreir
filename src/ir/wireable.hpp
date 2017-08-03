#ifndef WIREABLE_HPP_
#define WIREABLE_HPP_

#include "metadata.hpp"
#include "context.hpp"

using namespace std;

namespace CoreIR {

class InstanceGraphNode;

class Wireable {
  public:
    enum WireableKind {WK_Interface,WK_Instance,WK_Select};

  protected :
    WireableKind kind;
    ModuleDef* container; // ModuleDef which it is contained in 
    Type* type;

    unordered_set<Wireable*> connected; 
    unordered_map<string,Wireable*> selects;
    Metadata metadata;
  public :
    Wireable(WireableKind kind, ModuleDef* container, Type* type) : kind(kind),  container(container), type(type) {}
    virtual ~Wireable() {}
    virtual string toString() const=0;
    unordered_set<Wireable*> getConnectedWireables() { return connected;}
    unordered_map<string,Wireable*> getSelects() { return selects;}
    bool hasSel(string selstr) {return selects.count(selstr) >0;}
    Metadata getMetadata() { return metadata;}
    ModuleDef* getContainer() { return container;}
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
  
    //Connect this to w
    void connect(Wireable* w);

    //Disconnect everything from this wireable
    void disconnect();

    // if this wireable is from add3inst.a.b[0], then this will look like
    // {add3inst,a,b,0}
    SelectPath getSelectPath();
    ConstSelectPath getConstSelectPath();
    string wireableKind2Str(WireableKind wb);
    LocalConnections getLocalConnections();
    Wireable* getTopParent();
  protected :
    //This should be used very carefully. Could make things inconsistent
    friend class InstanceGraphNode;
    void setType(Type* t) {
      type = t;
    }
    void removeUnusedSelects();
};

ostream& operator<<(ostream&, const Wireable&);

class Interface : public Wireable {
  static const string instname;
  public :
    Interface(ModuleDef* container,Type* type) : Wireable(WK_Interface,container,type) {};
    static bool classof(const Wireable* w) {return w->getKind()==WK_Interface;}
    string toString() const;
    const string& getInstname() { return instname; }
};

class Instance : public Wireable {
  const string instname;
  Module* moduleRef = nullptr;
  
  Args configargs;
  
  bool isgen;
  bool wasgen = false;
  Generator* generatorRef = nullptr;
  Args genargs;
  
  public :
    Instance(ModuleDef* container, string instname, Module* moduleRef, Args configargs=Args());
    Instance(ModuleDef* container, string instname, Generator* generatorRef, Args genargs, Args configargs=Args());
    static bool classof(const Wireable* w) {return w->getKind()==WK_Instance;}
    string toString() const;
    json toJson();
    Module* getModuleRef() {return moduleRef;}
    const string& getInstname() { return instname; }
    Arg* getConfigArg(string s);
    Args getConfigArgs() const {return configargs;}
    bool hasConfigArgs() {return !configargs.empty();}
    
    //isGen means it is currently an instance of a generator
    //(Generator has NOT been run)
    bool isGen() const { return isgen;}

    //wasGen means it Was a generator AND the generator was run.
    //It still has genargs, but it also is referencing a module now.
    bool wasGen() const { return wasgen;}
    Generator* getGeneratorRef() { return generatorRef;}
    Instantiable* getInstantiableRef();
    Args getGenArgs() {return genargs;}
    
    //Returns if it actually ran the generator
    //Runs the generator and changes instance label to Module
    //Does NOT add the module to list of namespace modules
    //Module is owned by the generator. 
    //Call namespace.addModule(m) to move from generator to namespace
    bool runGenerator();

    void replace(Module* moduleRef, Args configargs=Args());
    void replace(Generator* generatorRef, Args genargs, Args configargs=Args());
  
  friend class InstanceGraphNode;
};

class Select : public Wireable {
  protected :
    Wireable* parent;
    string selStr;
  public :
    Select(ModuleDef* container, Wireable* parent, string selStr, Type* type) : Wireable(WK_Select,container,type), parent(parent), selStr(selStr) {}
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
    Select* newSelect(ModuleDef* container, Wireable* parent, string selStr,Type* t);
    //Warning this will delete s
    void eraseSelect(Select* s);
};


}//CoreIR namespace

#endif //WIREABLE_HPP_
