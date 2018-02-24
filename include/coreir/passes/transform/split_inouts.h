#ifndef SPLIT_INOUTS_PASS_HPP_
#define SPLIT_INOUTS_PASS_HPP_

#include "coreir.h"

namespace CoreIR {
  namespace Passes {

    class SplitInouts : public InstanceGraphPass {
    private :

    public:
      SplitInouts(std::string name) : InstanceGraphPass(name, "Break up each inout port into an input port and an output port") {}
      bool runOnInstanceGraphNode(InstanceGraphNode& node);
    };

  }
}
#endif
