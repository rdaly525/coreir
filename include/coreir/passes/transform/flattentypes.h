#ifndef FLATTENTYPES_HPP_
#define FLATTENTYPES_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class FlattenTypes : public InstanceGraphPass {
 private:
  // Get ports to be flattened
  void getPortList(
    Type* t,
    SelectPath cur,
    std::vector<std::pair<SelectPath, Type*>>& ports,
    std::vector<std::string>& uports);

  bool preserve_ndarrays = false;

  virtual bool isLeafType(Type* t);

 public:
  FlattenTypes()
      : InstanceGraphPass(
          "flattentypes",
          "Flattens the Type hierarchy to only bits or arrays of bits") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
  void initialize(int argc, char** argv) override;
};

}  // namespace Passes
}  // namespace CoreIR

#endif
