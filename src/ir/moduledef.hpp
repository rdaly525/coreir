#ifndef MODULEDEF_HPP_
#define MODULEDEF_HPP_


#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hpp"
#include "context.hpp"
#include "types.hpp"
#include "args.hpp"
#include "json.hpp"

#include "wireable.hpp"

using namespace std;

namespace CoreIR {

class ModuleDef {
    friend class Wireable;
  protected:
    Module* module;
    Interface* interface; 
    unordered_map<string,Instance*> instances;
    unordered_set<Connection> connections;
    SelCache* cache;
    SelCache* getCache() { return cache;}

    // Instances Iterator Internal Fields/API
    Instance* instancesIterFirst = nullptr;
    Instance* instancesIterLast = nullptr;
    unordered_map<Instance*,Instance*> instancesIterNextMap;
    unordered_map<Instance*,Instance*> instancesIterPrevMap;
    void appendInstanceToIter(Instance* instance);
    void removeInstanceFromIter(Instance* instance);
    
  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    unordered_map<string,Instance*> getInstances(void) { return instances;}
    unordered_set<Connection> getConnections(void) { return connections; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    
    //Return a shallow copy of this ModuleDef.
    ModuleDef* copy();
    Context* getContext();
    const string& getName();
    Type* getType();
    Module* getModule() { return module; }
    Interface* getInterface(void) {return interface;}

    //Can select using string (inst.port.subport)
    Wireable* sel(string s);
    //Or using a select Path
    Wireable* sel(SelectPath path);

    //Ignore these
    Wireable* sel(std::initializer_list<const char*> path);
    Wireable* sel(std::initializer_list<std::string> path);
    
    //API for adding an instance of either a module or generator
    Instance* addInstance(string instname,Generator* genref,Args genargs, Args config=Args());
    Instance* addInstance(string instname,Module* modref,Args config=Args());
    
    //Add instance using an Instantiable ref string
    Instance* addInstance(string instname,string iref,Args genOrConfigargs=Args(), Args configargs=Args());
    
    //copys info about i
    Instance* addInstance(Instance* i,string iname="");

    // API for iterating over instances
    Instance* getInstancesIterBegin() { return instancesIterFirst;}
    Instance* getInstancesIterEnd() { return nullptr;}
    Instance* getInstancesIterNext(Instance* instance);

    //API for connecting two instances together
    void connect(Wireable* a, Wireable* b);
    void connect(SelectPath pathA, SelectPath pathB);
    void connect(string pathA, string pathB); //dot notation a.b.c, e.f.g
    void connect(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB);
    void connect(std::initializer_list<std::string> pA, std::initializer_list<string> pB);
    
    bool hasConnection(Wireable* a, Wireable* b);
    Connection getConnection(Wireable* a, Wireable* b);

    //API for deleting a connection.
    void disconnect(Connection con);
    void disconnect(Wireable* a, Wireable* b);
    
    //This will disconnect everything the wireable is connected to
    void disconnect(Wireable* w);

    //API for deleting an instance
    //This will also delete all connections from all connected things
    void removeInstance(string inst);
    void removeInstance(Instance* inst);


    // This 'typechecks' everything
    //   Verifies all selects are valid
    //   Verifies all connections are valid. type <==> FLIP(type)
    //   Verifies inputs are only connected once
    //TODO Does not check if Everything (even inputs) is connected
    // Returns true if there is an error
    bool validate();
    
    json toJson();
    
};

}//CoreIR namespace
#endif // MODULEDEF_HPP
