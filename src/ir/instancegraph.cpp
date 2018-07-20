#include "coreir/ir/instancegraph.h"

using namespace std;
using namespace CoreIR;

void InstanceGraph::releaseMemory() {
  nodeMap.clear();
  for (auto ign : sortedNodes) delete ign;
  sortedNodes.clear();
}

bool InstanceGraph::validOnlyTop(InstanceGraphNode* node) {
  return onlyTopNodes.count(node->getModule()) > 0;
}

void InstanceGraph::sortVisit(InstanceGraphNode* node) {
  if (node->mark==2) {
    return;
  }
  ASSERT(node->mark!=1,"SOMEHOW not a DAG");
  node->mark = 1;
  for (auto nextnode : node->ignList) {
    sortVisit(nextnode);
  }
  node->mark = 2;
  sortedNodes.push_front(node);
}

namespace {
  void recurse(Module* m, std::unordered_set<Module*>& onlyTopNodes) {
    if (onlyTopNodes.count(m)) {
      return;
    }
    onlyTopNodes.insert(m);
    if (!m->hasDef()) {
      return;
    }
    for (auto ipair : m->getDef()->getInstances()) {
      Module* imod = ipair.second->getModuleRef();
      recurse(imod,onlyTopNodes);
    }
  }
}

void InstanceGraph::construct(Context* c) {

  //Contains all external nodes referenced

  if (c->hasTop()) {
    //Only do this on dependent nodes
    recurse(c->getTop(),onlyTopNodes);
  }
  
  for (auto nsmap : c->getNamespaces()) {
    for (auto imap : nsmap.second->getModules()) {
      nodeMap[imap.second] = new InstanceGraphNode(imap.second,false);
    }
  }

  //populate all the nodes with pointers to the instances
  unordered_map<Module*,InstanceGraphNode*> nodeMap2;
  for (auto nodemap : nodeMap) {
    nodeMap2.insert(nodemap);
  }
  for (auto nodemap : nodeMap2) {
    Module* m = nodemap.first;
    if (!m->hasDef()) continue;
    ModuleDef* mdef = cast<Module>(nodemap.first)->getDef();
    for (auto instmap : mdef->getInstances()) {
      Module* icheck = instmap.second->getModuleRef();
      ASSERT(nodeMap.count(icheck),"missing: " + icheck->toString());
      InstanceGraphNode* node = nodeMap[icheck];
      node->addInstance(instmap.second,nodemap.second);
    }
  }

  for (auto imap : nodeMap) {
    sortVisit(imap.second);
  }
}


void InstanceGraphNode::appendField(string label,Type* t) {
  auto m = getModule();
  RecordType* mtype = cast<RecordType>(m->getType());

  //appendField will assert if the field already exists
  RecordType* newType = mtype->appendField(label,t);

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

void InstanceGraphNode::detachField(string label) {
  Module* m = getModule();
  ASSERT(m->hasDef(),"NYI Handling changing types for module declaration");
  RecordType* mtype = cast<RecordType>(m->getType());

  //Will assert if field does not exist
  RecordType* newType = mtype->detachField(label);

  //Remove anything connected to the module def interface
  Interface* iface = m->getDef()->getInterface();
  iface->sel(label)->disconnectAll();
  iface->removeSel(label);

  //Remove anything connected to all the isntances
  for (auto inst : getInstanceList()) {
    inst->sel(label)->disconnectAll();

    inst->removeSel(label);
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

