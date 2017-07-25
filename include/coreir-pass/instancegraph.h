#ifndef INSTANCEGRAPH_HPP_
#define INSTANCEGRAPH_HPP_

#include "coreir.h"
#include "list"

namespace CoreIR {

class InstanceGraphNode;
class InstanceGraph {
  std::unordered_map<Instantiable*,InstanceGraphNode*> nodeMap;
  //std::unordered_map<Instantiable*,InstanceGraphNode*> externalNodeMap;
  std::list<InstanceGraphNode*> sortedNodes;
  public :
    InstanceGraph() {}
    ~InstanceGraph() {this->clear();}
    void construct(Namespace* ns);
    std::list<InstanceGraphNode*> getSortedNodes() { return sortedNodes;}
    void clear();
    void sortVisit(InstanceGraphNode* node);

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
