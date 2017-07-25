#ifndef FLATTENALLPASS_HPP_
#define FLATTENALLPASS_HPP_

#include "coreir.h"
#include "coreir-pass/passes.h"

using namespace CoreIR;

class FlattenAllPass : public InstanceGraphPass {
  public :
    FlattenAllPass() : InstanceGraphPass() {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) {
      bool changed = false;
      for (auto inst : node.getInstanceList()) {
        changed |= inlineInstance(inst);
      }
      return changed;
    }
};

#endif
