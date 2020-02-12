#ifndef VERIFYFLATTENDTYPES_HPP_
#define VERIFYFLATTENDTYPES_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class VerifyFlattenedTypes : public InstanceGraphPass {
  public :
    VerifyFlattenedTypes() : InstanceGraphPass(
        "verifyflattenedtypes",
        "Verify all modules and instances have flattened types",
        true
    ) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
};

}
}
#endif
