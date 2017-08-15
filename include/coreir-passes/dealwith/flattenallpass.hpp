#ifndef FLATTENALLPASS_HPP_
#define FLATTENALLPASS_HPP_

#include "coreir.h"

using namespace CoreIR;

class FlattenAllPass : public InstanceGraphPass {
  public :
    FlattenAllPass() : InstanceGraphPass() {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

#endif
