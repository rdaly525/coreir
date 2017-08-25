#include "coreir.h"
#include "treereductionpass.hpp"

//For convenient macros to create the registerPass and deletePass functions
#include "coreir-macros.h"

using namespace CoreIR;

//Do not forget to set this static variable!!
string TreeReductionPass::ID = "treereductionpass";

vector<Wireable*> TreeReductionPass::collectInputs(Instance* head) {
  vector<Wireable*> inputs;
  string opName = getOpName(head);

  // check in0 branch
  Instance* in0_inst = getSelectedInst(head, "in0");
  if (opName == getOpName(in0_inst)) {
    vector<Wireable*> in0_inputs = collectInputs(in0_inst);
    inputs.insert(inputs.end(), in0_inputs.begin(), in0_inputs.end());
  } else {
    inputs.push_back(head->sel("in0"));
  }

  // check in1 branch
  Instance* in1_inst = getSelectedInst(head, "in1");
  if (opName == getOpName(in1_inst)) {
    vector<Wireable*> in1_inputs = collectInputs(in1_inst);
    inputs.insert(inputs.end(), in1_inputs.begin(), in1_inputs.end());
  } else {
    inputs.push_back(head->sel("in1"));
  }

  return inputs;
}

bool TreeReductionPass::runOnModule(Module* m) {
  //Context* c = this->getContext();
  
  // early out if module is undefined
  if (!m->hasDef()) return false;
  ModuleDef* def = m->getDef();
  
  //Define our vector of instances to replace
  vector<Instance*> treeHeads;
  unordered_set<std::string> operators = {"add", "mul", "umin", "umax"};

  //Loop through all the instances 
  for (auto instmap : def->getInstances()) {
    Instance* inst = instmap.second;
    std::string opName = getOpName(inst);

    if (operators.count(opName)>0 && isAssocSubgraph(inst)) {
      Instance* in0Inst = getSelectedInst(inst, "in0");
      Instance* in1Inst = getSelectedInst(inst, "in1");
      if ((in0Inst != NULL && getOpName(in0Inst) == opName) ||
          (in1Inst != NULL && getOpName(in1Inst) == opName)) {
        cout << "found inst to replace" << endl;
        treeHeads.push_back(inst);
      }
    }
  }

  //Loop through all instances and replace with a tree implementation
  for (auto headInst : treeHeads) {

    // found boundary interface for reduction tree
    vector<Wireable*> inputs = collectInputs(headInst);
    cout << headInst->toString() << " has the inputs:" << endl;
    for (auto inst : inputs) {
      cout << " " << inst->toString();
    }

    // create tree version
    // create passthroughs
    // remove old instances
    // wire up new tree version
  }

  //Add this current module to the user datastructure we defined before
  if (getTotalSubgraphs() > 0 ) {
    cout << "found some stuff" << endl;
  }
  return false;
}

string TreeReductionPass::getOpName(Instance* i) {
  std::string opName = i->getInstantiableRef()->getName();
  return opName;
}

Instance* TreeReductionPass::getSelectedInst(Instance* i, string sel) {
  if (!i->hasSel(sel)) {
    return NULL;
  }

  Select* connectedSel = NULL;
  LocalConnections conxs = i->getLocalConnections();
  for (auto conx : conxs) {
    Select* thisWire = static_cast<Select*>(conx.first);

    if (thisWire->getSelStr() == sel) {
      //cout << conx.first->toString() << " connected to " << conx.second->toString() << endl;
      if (conx.second->getKind() != Wireable::WireableKind::WK_Select) { continue; }
      connectedSel = static_cast<Select*>(conx.second);
    }
  }
  if (connectedSel == NULL) { return NULL; }

  Wireable* parentWire = connectedSel->getParent();
  if (parentWire->getKind() != Wireable::WireableKind::WK_Instance) { return NULL; }

  Instance* parentInst = static_cast<Instance*>(parentWire);
  return parentInst;
}

// identify if this is the top of a series of the same operator
bool TreeReductionPass::isAssocSubgraph(Instance* i) {
  Instance* parentInst = getSelectedInst(i, "out");
  if (parentInst == NULL) { return true; }

  std::string opName = getOpName(i);
  std::string parentOpName = getOpName(parentInst);

  // cout << "  " << i->toString() << "  connected to " << parentWire->toString() << endl;
  // cout << "  " << opName << "  connected to " << parentOpName << endl;

  if (parentOpName == opName) {
    cout << "  " << i->toString() << " is not the parent" << endl;
    return false;
  } else {
    return true;
  }
}

int TreeReductionPass::getTotalSubgraphs() {
  return targetSubgraphs.size();
}

void TreeReductionPass::print() {
  cout << "This is a test" << endl;
}

//This is the macro that will define the registerPass and deletePass functions for you.
COREIR_GEN_EXTERNAL_PASS(TreeReductionPass);
