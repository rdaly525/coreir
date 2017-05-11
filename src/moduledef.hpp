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
  
  protected:
    Module* module;
    Interface* interface; 
    unordered_map<string,Instance*> instances;
    unordered_set<Connection> connections;
    SelCache* cache;
    Metadata metadata;
    Metadata implementations; // TODO maybe have this just be inhereted moduledef classes

  public :
    ModuleDef(Module* m);
    ~ModuleDef();
    //SelCache* getCache(void) { return cache;}
    unordered_map<string,Instance*> getInstances(void) { return instances;}
    unordered_set<Connection> getConnections(void) { return connections; }
    bool hasInstances(void) { return !instances.empty();}
    void print(void);
    Context* getContext();
    string getName();
    Type* getType();
    SelCache* getCache() { return cache;}
    Metadata getMetadata() { return metadata;}
    Module* getModule() { return module; }
    Instance* addInstance(string,Generator*,Args genargs, Args config=Args());
    Instance* addInstance(string,Module*,Args config=Args());
    Instance* addInstance(Instance* i); //copys info about i
    Interface* getInterface(void) {return interface;}
    Wireable* sel(string s);
    Wireable* sel(SelectPath path);
    void wire(Wireable* a, Wireable* b);
    void wire(SelectPath pathA, SelectPath pathB);
    void wire(string pathA, string pathB);
    void wire(std::initializer_list<const char*> pA, std::initializer_list<const char*> pB) {
      wire(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
    }
    void wire(std::initializer_list<std::string> pA, std::initializer_list<string> pB) {
      wire(SelectPath(pA.begin(),pA.end()),SelectPath(pB.begin(),pB.end()));
    }

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
