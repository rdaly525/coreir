#ifndef FLATTENTYPES_HPP_
#define FLATTENTYPES_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class FlattenTypes : public InstanceGraphPass {
  public :
    FlattenTypes() : InstanceGraphPass("flattentypes","Flattens the Type hierarchy to only bits or arrays of bits") {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
};

}
}

#endif
