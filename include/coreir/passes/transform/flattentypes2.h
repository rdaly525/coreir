#ifndef FLATTENTYPES2_HPP_
#define FLATTENTYPES2_HPP_

#include "coreir/passes/transform/flattentypes.h"

namespace CoreIR {
namespace Passes {

class FlattenTypes2 : public FlattenTypes {
 protected:
  bool isLeafType(Type* t) override;

 public:
  FlattenTypes2()
      : FlattenTypes(
          "flattentypes2",
          "Flattens the Type hierarchy to only bits or multi-dimensional "
          "arrays of bits") {}
  using FlattenTypes::runOnInstanceGraphNode;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
