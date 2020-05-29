#ifndef HELLOT_HPP_
#define HELLOT_HPP_

#include "ir/coreir.h"

namespace CoreIR {
namespace Passes {

class HelloT : public NamespacePass {
 public:
  static std::string ID;

  HelloT() : NamespacePass(ID, "Hello Transform") {}
  bool runOnNamespace(Namespace* ns) override;
  void setAnalysisInfo() override { addDependency("helloa"); }
};

}  // namespace Passes
}  // namespace CoreIR

#endif
