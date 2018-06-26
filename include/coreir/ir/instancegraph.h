#ifndef INSTANCEGRAPH_HPP_
#define INSTANCEGRAPH_HPP_

#include "coreir.h"
#include "list"

namespace CoreIR {

class InstanceGraphNode;
class InstanceGraph {
  std::unordered_map<Module*,InstanceGraphNode*> nodeMap;
  std::unordered_set<Module*> onlyTopNodes;
  std::list<InstanceGraphNode*> sortedNodes;
  public :
    InstanceGraph() {}
    ~InstanceGraph() {this->releaseMemory();}
    void construct(Context* c);
    std::list<InstanceGraphNode*> getSortedNodes() { return sortedNodes;}
    bool validOnlyTop(InstanceGraphNode* node);
    void releaseMemory();
    void sortVisit(InstanceGraphNode* node);

};

class InstanceGraphNode {
  //The underlying instantiable
  Module* m;
  typedef std::vector<Instance*> InstanceList;
  InstanceList instanceList;
  bool external;
  public:
    InstanceGraphNode(Module* m,bool external) : m(m), external(external) {}
    //Returns a list of instances that instantiate THIS instantiable (Kind of like a Use-def
    InstanceList getInstanceList() { return instanceList;}
    Module* getModule() { return m;}

    bool isExternal() {return external;}

    //Add a new field (port) to this node
    //Only works with Modules. 
    void appendField(std::string label,Type* t);
    
    //Remove port from this instance
    //Will disconnect anything connected to this port both in the module and all instances
    void detachField(std::string label);

  private:
    std::vector<InstanceGraphNode*> ignList;
    int mark=0; //unmarked=0, temp=1,perm=2
    void addInstance(Instance* i, InstanceGraphNode* ign) { 
      instanceList.push_back(i);
      ignList.push_back(ign);
    }

  friend class InstanceGraph;
};

}
#endif //INSTANCEGRAPH_HPP_
