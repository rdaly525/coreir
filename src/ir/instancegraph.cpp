#include "coreir/ir/instancegraph.h"

using namespace std;
using namespace CoreIR;

bool InstanceGraph::ModuleCmp::operator()(const Module* l, const Module* r)
  const {
  return l->getLongName() < r->getLongName();
}

void InstanceGraph::releaseMemory() {
  nodeMap.clear();
  for (auto ign : sortedNodes) delete ign;
  sortedNodes.clear();
}

void InstanceGraph::sortVisit(InstanceGraphNode* node) {
  if (node->mark == 2) { return; }
  ASSERT(node->mark != 1, "SOMEHOW not a DAG");
  node->mark = 1;
  for (auto nextnode : node->ignList) { sortVisit(nextnode); }
  node->mark = 2;
  sortedNodes.push_front(node);
}

void InstanceGraph::construct(Context* c) {

  // Contains all external nodes referenced
  for (auto nsmap : c->getNamespaces()) {
    for (auto imap : nsmap.second->getModules()) {
      nodeMap[imap.second] = new InstanceGraphNode(imap.second, false);
    }
  }

  // populate all the nodes with pointers to the instances
  map<Module*, InstanceGraphNode*, InstanceGraph::ModuleCmp> nodeMap2;
  for (auto nodemap : nodeMap) { nodeMap2.insert(nodemap); }
  for (auto nodemap : nodeMap2) {
    Module* m = nodemap.first;
    if (m->hasLinkedModule()) {
      if (m->hasDefaultLinkedModule()) {
        InstanceGraphNode* node = nodeMap[m->getDefaultLinkedModule()];
        node->addInstanceGraphNode(nodemap.second);
      }
      for (auto entry : m->getLinkedModules()) {
        InstanceGraphNode* node = nodeMap[entry.second];
        node->addInstanceGraphNode(nodemap.second);
      }
    }
    if (!m->hasDef()) continue;
    ModuleDef* mdef = cast<Module>(nodemap.first)->getDef();
    for (auto instmap : mdef->getInstances()) {
      Module* icheck = instmap.second->getModuleRef();
      ASSERT(nodeMap.count(icheck), "missing: " + icheck->toString());
      InstanceGraphNode* node = nodeMap[icheck];
      node->addInstance(instmap.second, nodemap.second);
    }
  }

  for (auto imap : nodeMap) { sortVisit(imap.second); }
}

namespace {
void getAllDependentModules(
  Module* m,
  std::set<Module*, InstanceGraph::ModuleCmp>& onlyTopNodes) {
  if (onlyTopNodes.count(m)) { return; }
  onlyTopNodes.insert(m);
  if (m->hasLinkedModule()) {
    if (m->hasDefaultLinkedModule()) {
      getAllDependentModules(m->getDefaultLinkedModule(), onlyTopNodes);
    }
    for (auto entry : m->getLinkedModules()) {
      getAllDependentModules(entry.second, onlyTopNodes);
    }
    return;
  }
  if (!m->hasDef()) { return; }
  for (auto ipair : m->getDef()->getInstances()) {
    Module* imod = ipair.second->getModuleRef();
    getAllDependentModules(imod, onlyTopNodes);
  }
}
}  // namespace

std::list<InstanceGraphNode*> InstanceGraph::getFilteredNodes(std::vector<Module*>& mods) {
  if (mods.size()==0) {
    return this->getSortedNodes();
  }

  std::set<Module*, InstanceGraph::ModuleCmp> filteredModules;
  for (auto m : mods) { getAllDependentModules(m, filteredModules);
  }
  std::list<InstanceGraphNode*> ret;
  for (auto inode : this->getSortedNodes()) {
    if (filteredModules.count(inode->getModule()) >0) {
      ret.push_back(inode);
    }
  }
  return ret;
}


void InstanceGraphNode::appendField(string label, Type* t) {
  auto m = getModule();
  RecordType* mtype = cast<RecordType>(m->getType());

  // appendField will assert if the field already exists
  RecordType* newType = mtype->appendField(label, t);

  // Do not have to check any connections because I am adding a new field

  // First change the Module Type
  m->setType(newType);

  // Then change Interface of module def (if exists)
  if (m->hasDef()) {
    m->getDef()->getInterface()->setType(newType->getFlipped());
  }

  // Finally change all the instances
  for (auto inst : getInstanceList()) { inst->setType(newType); }
}

void InstanceGraphNode::detachField(string label) {
  Module* m = getModule();
  RecordType* mtype = cast<RecordType>(m->getType());

  // Will assert if field does not exist
  RecordType* newType = mtype->detachField(label);

  if (m->hasDef()) {
    // Remove anything connected to the module def interface
    Interface* iface = m->getDef()->getInterface();
    iface->sel(label)->disconnectAll();
    iface->removeSel(label);
  }

  // Remove anything connected to all the isntances
  for (auto inst : getInstanceList()) {
    inst->sel(label)->disconnectAll();

    inst->removeSel(label);
  }

  // First change the Module Type
  m->setType(newType);

  // Then change Interface of module def (if exists)
  if (m->hasDef()) {
    m->getDef()->getInterface()->setType(newType->getFlipped());
  }

  // Finally change all the instances
  for (auto inst : getInstanceList()) { inst->setType(newType); }
}
