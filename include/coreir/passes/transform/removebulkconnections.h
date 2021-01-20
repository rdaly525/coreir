#ifndef REMOVEBULKCONNECTIONS_HPP_
#define REMOVEBULKCONNECTIONS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveBulkConnections : public ModulePass {
 public:
  RemoveBulkConnections()
      : ModulePass(
          "removebulkconnections",
          "Removes any bulk connections. Only connections will be bits and "
          "arrays of bits") {}
  bool runOnModule(Module* m) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
