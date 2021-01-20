#ifndef HELLOT_HPP_
#define HELLOT_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class HelloT : public NamespacePass {
 public:
  HelloT() : NamespacePass("hellot", "Hello Transform") {}
  bool runOnNamespace(Namespace* ns) override;
  void setAnalysisInfo() override { addDependency("helloa"); }
};

}  // namespace Passes
}  // namespace CoreIR

#endif
