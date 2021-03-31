#ifndef COREIRJSON_HPP_
#define COREIRJSON_HPP_

#include <map>
#include "coreir.h"
#include "coreir/passes/analysis/coreir_json_lib.h"

namespace CoreIR {
namespace Passes {

class CoreIRJson : public NamespacePass {

  std::map<std::string, std::string> nsMap;

 public:
  CoreIRJson()
      : NamespacePass("coreirjson", "Creates a json of the coreir", true) {}
  bool runOnNamespace(Namespace* ns) override;
  void writeToStream(std::ostream& os, std::string topRef) override;
  void writeToStream(std::ostream& os) override;
};

class CoreIRSerialize : public InstanceGraphPass {
  std::map<std::string, JsonLib::NamespaceJson> nss;
  bool headerOnly = false;
 public:
  CoreIRSerialize()
    : InstanceGraphPass("serialize", "Creates a json of a single circuit", true) {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
  void initialize(int argc, char** argv) override;
  void writeToStream(std::ostream& os) override;
  void releaseMemory() override;

  JsonLib::NamespaceJson& getOrCreateNamespace(Namespace* ns);
};

}  // namespace Passes
}  // namespace CoreIR
#endif
