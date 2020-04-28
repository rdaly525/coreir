#ifndef COREIR_PRINTER_HPP_
#define COREIR_PRINTER_HPP_

#include <ostream>
#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Printer : public ContextPass {
 public:
  static std::string ID;
  Printer() : ContextPass(ID, "Prints", true) {}
  bool runOnContext(Context* c) override;
  void setAnalysisInfo() override { addDependency("coreirjson"); }
};

}  // namespace Passes
}  // namespace CoreIR

#endif
