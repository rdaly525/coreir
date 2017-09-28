#ifndef COREIR_WIREABLE_HPP_
#define COREIR_WIREABLE_HPP_

#include "fwd_declare.h"
#include "metadata.h"

namespace CoreIR {

class InstanceGraphNode;

class Wireable : public MetaData {
  public:
    enum WireableKind {WK_Interface,WK_Instance,WK_Select};

  protected :
    WireableKind kind;
    ModuleDef* container; // ModuleDef which it is contained in 
    Type* type;

    std::unordered_set<Wireable*> connected; 
    
    //This manages the memory for the selects
    std::unordered_map<std::string,Select*> selects;
  public :
    Wireable(WireableKind kind, ModuleDef* container, Type* type) : MetaData(), kind(kind),  container(container), type(type) {}
    virtual ~Wireable();
    virtual std::string toString() const=0;
    std::unordered_set<Wireable*> getConnectedWireables() { return connected;}
    std::unordered_map<std::string,Select*> getSelects() { return selects;}
    bool hasSel(std::string selstr) {return selects.count(selstr) >0;}
    ModuleDef* getContainer() { return container;}
    Context* getContext();
    WireableKind getKind() const { return kind; }
    Type* getType() { return type;}
    void addConnectedWireable(Wireable* w) { connected.insert(w); }
    void removeConnectedWireable(Wireable* w) {
      assert(connected.count(w) > 0);
      connected.erase(w);
    }
    
    Select* sel(std::string);
    Select* sel(uint);
    Select* sel(SelectPath);
    
    //Ignore These
    Select* sel(std::initializer_list<const char*> path);
    Select* sel(std::initializer_list<std::string> path);
  
    bool canSel(std::string);
  
    //Connect this to w
    void connect(Wireable* w);

    //Disconnect everything from this wireable
    void disconnect();
    void disconnectAll();

    // if this wireable is from add3inst.a.b[0], then this will look like
    // {add3inst,a,b,0}
    SelectPath getSelectPath();
    ConstSelectPath getConstSelectPath();
    std::string wireableKind2Str(WireableKind wb);
    LocalConnections getLocalConnections();
    Wireable* getTopParent();

    //removes the select from this wireble.
    void removeSel(std::string selStr);


  protected :
    //This should be used very carefully. Could make things inconsistent
    friend class InstanceGraphNode;
    void setType(Type* t) {
      type = t;
    }
};

std::ostream& operator<<(std::ostream&, const Wireable&);

class Interface : public Wireable {
  static const std::string instname;
  public :
    Interface(ModuleDef* container,Type* type) : Wireable(WK_Interface,container,type) {};
    static bool classof(const Wireable* w) {return w->getKind()==WK_Interface;}
    std::string toString() const;
    const std::string& getInstname() { return instname; }
};

class Instance : public Wireable {
  const std::string instname;
  Module* moduleRef = nullptr;
  
  Values modargs;
  
  bool isgen;
  bool wasgen = false;
  Generator* generatorRef = nullptr;
  Values genargs;
  
  public :
    Instance(ModuleDef* container, std::string instname, Module* moduleRef, Values modargs=Values());
    Instance(ModuleDef* container, std::string instname, Generator* generatorRef, Consts genargs, Values modargs=Values());
    static bool classof(const Wireable* w) {return w->getKind()==WK_Instance;}
    std::string toString() const;
    json toJson();
    Module* getModuleRef() {return moduleRef;}
    const std::string& getInstname() const { return instname; }
    const Values& getModArgs() const {return modargs;}
    bool hasModArgs() {return !modargs.empty();}
    
    //isGen means it is currently an instance of a generator
    //(Generator has NOT been run)
    bool isGen() const { return isgen;}

    //wasGen means it Was a generator AND the generator was run.
    //It still has genargs, but it also is referencing a module now.
    bool wasGen() const { return wasgen;}
    Generator* getGeneratorRef() { return generatorRef;}
    Instantiable* getInstantiableRef();
    const Values& getGenArgs() const {return genargs;}
    
    //Returns if it actually ran the generator
    //Runs the generator and changes instance label to Module
    //Does NOT add the module to list of namespace modules
    //Module is owned by the generator. 
    //Call namespace.addModule(m) to move from generator to namespace
    bool runGenerator();

    void replace(Module* moduleRef, Values modargs=Values());
    void replace(Generator* generatorRef, Values genargs, Values modargs=Values());
  
  friend class InstanceGraphNode;
};

class Select : public Wireable {
  protected :
    Wireable* parent;
    std::string selStr;
  public :
    Select(ModuleDef* container, Wireable* parent, std::string selStr, Type* type) : Wireable(WK_Select,container,type), parent(parent), selStr(selStr) {}
    static bool classof(const Wireable* w) {return w->getKind()==WK_Select;}
    std::string toString() const;
    Wireable* getParent() { return parent; }
    const std::string& getSelStr() { return selStr; }
};

}//CoreIR namespace

#endif //WIREABLE_HPP_
