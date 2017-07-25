#include "coreir-pass/instancegraph.h"

using namespace CoreIR;

void InstanceGraph::construct(Namespace* ns) {
  
  //Contains all external nodes referenced
  //unordered_map<Instantiable*,InstanceGraphNode*> externalNodeMap;
  
  //Create all Nodes first
  for (auto imap : ns->getModules()) {
    nodeMap[imap.second] = new InstanceGraphNode(imap.second,false);
  }
  for (auto imap : ns->getGenerators()) {
    nodeMap[imap.second] = new InstanceGraphNode(imap.second,false);
  }
  
  //populate all the nodes with pointers to the instances
  for (auto nodemap : nodeMap) {
    if (isa<Generator>(nodemap.first) || !nodemap.first->hasDef()) continue;
    ModuleDef* mdef = cast<Module>(nodemap.first)->getDef();
    for (auto instmap : mdef->getInstances()) {
      Instantiable* icheck = instmap.second->getInstantiableRef();
      if (nodeMap.count(icheck)==0) {
        auto node = new InstanceGraphNode(icheck,true);
        nodeMap[icheck] = node;
        //externalNodeMap[icheck] = node;
      }
      nodeMap[icheck]->addInstance(instmap.second);
    }
  }

  //TODO sort this 
  for (auto imap : nodeMap) {
    sortedNodes.push_back(imap.second);
  }
}

