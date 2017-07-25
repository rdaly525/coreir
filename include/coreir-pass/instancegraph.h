#ifndef INSTANCEGRAPH_HPP_
#define INSTANCEGRAPH_HPP_

#include "coreir.h"

namespace CoreIR {

class InstanceGraphNode;
class InstanceGraph {
  std::unordered_map<Instantiable*,InstanceGraphNode*> nodeMap;
  std::unordered_map<Instantiable*,InstanceGraphNode*> externalNodeMap;
  std::vector<InstanceGraphNode*> sortedNodes;
  public :
    InstanceGraph() {}
    void construct(Namespace* ns);
    std::vector<InstanceGraphNode*> getSortedNodes() { return sortedNodes;}

};

class InstanceGraphNode {
  //The underlying instantiable
  Instantiable* i;
  typedef std::vector<Instance*> InstanceList;
  InstanceList instanceList;
  bool external;
  public:
    InstanceGraphNode(Instantiable* i,bool external) : i(i), external(external) {}
    InstanceList getInstanceList() { return instanceList;}
    Instantiable* getInstantiable() { return i;}

    bool isExternal() {return external;}

    //TODO probably unstable with generators
    //Add a port to this node
    //void appendToRecord(string label,Type* t);
    
    //Remove port from this instance
    //Will disconnect anything connected to this port both in the module and externally
    //void detachFromRecord(string label);

  private:
    void addInstance(Instance* i) { instanceList.push_back(i);}
  friend class InstanceGraph;
};

}
#endif //INSTANCEGRAPH_HPP_
