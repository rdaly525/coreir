#include "coreir.h"
#include "assert_pass.h"

using namespace CoreIR;

void testBlackboxVerilog() {
  Context* c = newContext();
  Module* top;

  if (!loadFromFile(c, "blackbox_verilog_in.json", &top)) {
    c->die();
  }
  assert(top != nullptr);
  c->setTop(top->getRefName());

  const std::vector<std::string> passes = {
    "rungenerators",
    "removebulkconnections",
    "flattentypes",
    "verilog --inline"
  };
  c->runPasses(passes, {});
  assertPassEq<Passes::Verilog>(c, "blackbox_verilog_golden.v");
  
  deleteContext(c);
}

int main() {
  testBlackboxVerilog();
}
