#include "instancegraph.h"

using namespace CoreIR;

void InstanceGraph::clear() {
  nodeMap.clear();
  for (auto ign : sortedNodes) delete ign;
  sortedNodes.clear();
}

void InstanceGraph::sortVisit(InstanceGraphNode* node) {
  if (node->mark==2) return;
  ASSERT(node->mark!=1,"SOMEHOW not a DAG");
  node->mark = 1;
  for (auto nextnode : node->ignList) {
    sortVisit(nextnode);
  }
  node->mark = 2;
  sortedNodes.push_front(node);
}

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
      nodeMap[icheck]->addInstance(instmap.second,nodemap.second);
    }
  }

  for (auto imap : nodeMap) {
    sortVisit(imap.second);
  }
}


void InstanceGraphNode::appendField(string label,Type* t) {
  auto i = getInstantiable();
  if (isa<Generator>(i)) {
    ASSERT(0,"NYI Handling changing generator types");
  }
  Module* m = cast<Module>(i);
  RecordType* mtype = cast<RecordType>(m->getType());

  //appendField will assert if the field already exists
  Type* newType = mtype->appendField(label,t);
  
  //Do not have to check any connections because I am adding a new field
  
  //First change the Module Type
  m->setType(newType);

  //Then change Interface of module def (if exists)
  if (m->hasDef()) {
    m->getDef()->getInterface()->setType(newType->getFlipped());
  }

  //Finally change all the instances
  for (auto inst : getInstanceList()) {
    inst->setType(newType);
  }
}




void disconnectAll(Wireable* w) {
  for (auto sw : w->getSelects()) {
    disconnectAll(sw.second);
  }
  w->disconnect();
}
void InstanceGraphNode::detachField(string label) {
  auto i = getInstantiable();
  if (isa<Generator>(i)) {
    ASSERT(0,"NYI Handling changing generator types");
  }
  Module* m = cast<Module>(i);
  RecordType* mtype = cast<RecordType>(m->getType());
  
  //Will assert if field does not exist
  Type* newType = mtype->detachField(label);
  
  //Remove anything connected to the module def interface
  if (m->hasDef()) {
    Interface* iface = m->getDef()->getInterface();
    disconnectAll(iface->sel(label));
    iface->sel(label)->removeUnusedSelects();
  }
  
  //Remove anything connected to all the isntances
  for (auto inst : getInstanceList()) {
    disconnectAll(inst->sel(label));
    inst->sel(label)->removeUnusedSelects();
  }

  //First change the Module Type
  m->setType(newType);

  //Then change Interface of module def (if exists)
  if (m->hasDef()) {
    m->getDef()->getInterface()->setType(newType->getFlipped());
  }

  //Finally change all the instances
  for (auto inst : getInstanceList()) {
    inst->setType(newType);
  }
}

