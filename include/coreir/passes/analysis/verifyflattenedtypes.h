#ifndef VERIFYFLATTENDTYPES_HPP_
#define VERIFYFLATTENDTYPES_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class VerifyFlattenedTypes : public InstanceGraphPass {
  public :
    static std::string ID;
    VerifyFlattenedTypes() : InstanceGraphPass(ID,"Verify all modules and instances have flattened types",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
};

}
}
#endif
