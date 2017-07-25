#ifndef FLATTENALLPASS_HPP_
#define FLATTENALLPASS_HPP_

#include "coreir.h"
#include "coreir-pass/passes.h"

using namespace CoreIR;

class FlattenAllPass : public InstanceGraphPass {
  public :
    FlattenAllPass() : InstanceGraphPass() {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) {
      cout << "Working on Node!" << node.getInstantiable()->getName() << endl;
      bool changed = false;
      for (auto insts : node.getInstanceList()) {
        changed |= inlineInstance(insts);
      }
      return changed;
    }
};

#endif
