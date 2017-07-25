#ifndef FLATTENALLPASS_HPP_
#define FLATTENALLPASS_HPP_

#include "coreir.h"
#include "coreir-pass/passes.h"

using namespace CoreIR;

class FlattenAllPass : public InstanceGraphPass {
  public :
    FlattenAllPass() : InstanceGraphPass() {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) {
      cout << "{" << endl;
      cout << "Working on Node!" << node.getInstantiable()->getName() << endl;
      cout << "isGen" << isa<Generator>(node.getInstantiable()) << endl;
      bool changed = false;
      for (auto inst : node.getInstanceList()) {
        cout << "Inlining: " << inst->getInstname() << endl;
        changed |= inlineInstance(inst);
      }
      cout << "}" << endl;
      return changed;
    }
};

#endif
