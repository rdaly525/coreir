#pragma once

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class InstanceCount : public InstanceGraphPass {
  std::set<Module*> missingDefs;
  // First int is the number of instancs in local module.
  // Second int is numer of instances in the bottom module
  std::map<Module*, std::map<std::string, std::pair<int, int>>> cntMap;
  std::vector<Module*> modOrder;

 public:
  InstanceCount() : InstanceGraphPass("instancecount", "", true) {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
  // void initialize(int argc, char** argv) override;

  // void writeToStream(std::ostream& os);
  // void writeToFiles(const std::string& dir);

  bool finalize() override;
};

}  // namespace Passes
}  // namespace CoreIR
