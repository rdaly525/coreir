#ifndef COREIRJSON_HPP_
#define COREIRJSON_HPP_

#include <map>
#include "coreir.h"

namespace CoreIR {
namespace Passes {

class CoreIRJson : public NamespacePass {

  std::map<std::string, std::string> nsMap;

 public:
  CoreIRJson()
      : NamespacePass("coreirjson", "Creates a json of the coreir", true) {}
  bool runOnNamespace(Namespace* ns) override;
  void writeToStream(std::ostream& os, std::string topRef) override;
};

}  // namespace Passes
}  // namespace CoreIR
#endif
