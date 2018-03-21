#pragma once

#include "coreir.h"

namespace CoreIR {
  namespace Passes {

    class DeleteUnusedInouts : public InstanceGraphPass {
    private :

    public:
      SplitInouts(std::string name) : InstanceGraphPass(name, "Remove and ports that are not used") {}
      bool runOnInstanceGraphNode(InstanceGraphNode& node);
    };

  }
}
#endif
