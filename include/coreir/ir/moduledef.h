#ifndef COREIR_MODULEDEF_HPP_
#define COREIR_MODULEDEF_HPP_


#include "fwd_declare.h"
#include "context.h"
#include "module.h"
#include "wireable.h"

namespace CoreIR {

//struct ConnectionHasher {
//  size_t operator()(const Connection& rp) const {
//    size_t hash = 0;
//    hash_combine(hash,rp.first);
//    hash_combine(hash,rp.second);
//    return hash;
//  }
//};


class ModuleDef {
    friend class Wireable;
  protected:
    Module* module;
    Interface* interface; 
    std::map<std::string,Instance*> instances;
    std::set<Connection,ConnectionComp> connections;

    
    // Instances Iterator Internal Fields/API
    Instance* instancesIterFirst = nullptr;
    Instance* instancesIterLast = nullptr;
    std::unordered_map<Instance*,Instance*> instancesIterNextMap;
    std::unordered_map<Instance*,Instance*> instancesIterPrevMap;
    void appendInstanceToIter(Instance* instance);
    void removeInstanceFromIter(Instance* instance);
    
  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    const std::map<std::string,Instance*>& getInstances(void) const { return instances;}
    const std::set<Connection,ConnectionComp>& getConnections(void) const { return connections; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    
    //Return a shallow copy of this ModuleDef.
    ModuleDef* copy();
    Context* getContext();
    const std::string& getName();
    RecordType* getType();
    Module* getModule() { return module; }
    Interface* getInterface(void) {return interface;}

    bool canSel(const std::string& selstr);
    bool canSel(SelectPath path);
    //Can select using std::string (inst.port.subport)
    Wireable* sel(const std::string& s);
    //Or using a select Path
    Wireable* sel(const SelectPath& path);

    //Ignore these
    Wireable* sel(std::initializer_list<const char*> path);
    Wireable* sel(std::initializer_list<std::string> path);
    

    //API for adding an instance of either a module or generator
    Instance* addInstance(std::string instname,Generator* genref,Values genargs, Values modargs=Values());
    Instance* addInstance(std::string instname,Module* modref,Values modargs=Values());
    
    //Add instance using a GlobalValue ref std::string
    Instance* addInstance(std::string instname,std::string iref,Values genOrModargs=Values(), Values modargs=Values());
    
    //copys info about i
    Instance* addInstance(Instance* i,std::string iname="");

    // API for iterating over instances
    Instance* getInstancesIterBegin() { return instancesIterFirst;}
    Instance* getInstancesIterEnd() { return nullptr;}
    Instance* getInstancesIterNext(Instance* instance);

    //API for connecting two instances together
    void connect(Wireable* a, Wireable* b);
    void connect(const SelectPath& pathA, const SelectPath& pathB);
    void connect(const std::string& pathA, const std::string& pathB); //dot notation a.b.c, e.f.g
    void connect(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB);
    void connect(std::initializer_list<std::string> pA, std::initializer_list<std::string> pB);
    
    bool hasConnection(Wireable* a, Wireable* b);
    Connection getConnection(Wireable* a, Wireable* b);

    //API for deleting a connection.
    void disconnect(Connection con);
    void disconnect(Wireable* a, Wireable* b);
    
    //This will disconnect everything the wireable is connected to
    void disconnect(Wireable* w);

    //API for deleting an instance
    //This will also delete all connections from all connected things
    ////Note these will invalidate iterators from the following: getInstances(), getConnections(), getConnectedWireables()
    void removeInstance(std::string inst);
    void removeInstance(Instance* inst);


    // This 'typechecks' everything
    //   Verifies all selects are valid
    //   Verifies all connections are valid. type <==> FLIP(type)
    //   Verifies inputs are only connected once
    //TODO Does not check if Everything (even inputs) is connected
    // Returns true if there is an error
    bool validate();
    bool checkTypes(Wireable* a, Wireable* b);
};

}//CoreIR namespace
#endif // MODULEDEF_HPP
