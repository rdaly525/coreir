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
#include "metadata.hpp"

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
    Metadata metadata;
    Metadata implementations; // TODO maybe have this just be inhereted moduledef classes
    SelCache* getCache() { return cache;}
    
  public:
    typedef unordered_map<Instantiable*,unordered_set<Instance*>> InstanceMapType;
  protected:
    //Map from Instantiables to a list of instances
    InstanceMapType instanceMap;
  
  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    unordered_map<string,Instance*> getInstances(void) { return instances;}
    unordered_set<Connection> getConnections(void) { return connections; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    
    //Return a shalow copy of this ModuleDef.
    ModuleDef* copy();
    Context* getContext();
    string getName();
    Type* getType();
    Metadata getMetadata() { return metadata;}
    Module* getModule() { return module; }
    Interface* getInterface(void) {return interface;}
    
    InstanceMapType getInstanceMap() { return instanceMap;}
    

    Wireable* sel(string s);
    Wireable* sel(SelectPath path);
    
    //API for adding an instance of either a module or generator
    Instance* addInstance(string,Generator*,Args genargs, Args config=Args());
    Instance* addInstance(string,Module*,Args config=Args());
    Instance* addInstance(Instance* i,string iname=""); //copys info about i

    //API for connecting two instances together
    void connect(Wireable* a, Wireable* b);
    void connect(SelectPath pathA, SelectPath pathB);
    void connect(string pathA, string pathB);
    void connect(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB);
    void connect(std::initializer_list<std::string> pA, std::initializer_list<string> pB);
    
    //API for deleting a connection.
    //This will also delete the references from the wireable
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
