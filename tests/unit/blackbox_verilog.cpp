#include <fstream>
#include <streambuf>
#include "coreir.h"
#include "coreir/passes/analysis/verilog.h"

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
    "verilog"
  };
  c->runPasses(passes, {});
  auto vpass = static_cast<Passes::Verilog*>(
      c->getPassManager()->getAnalysisPass("verilog"));
  std::ostringstream stream;
  vpass->writeToStream(stream);
  const std::string verilog = stream.str();

  std::ifstream golden_stream("blackbox_verilog_golden.v");
  std::string golden((std::istreambuf_iterator<char>(golden_stream)),
                     std::istreambuf_iterator<char>());
  ASSERT(golden == verilog,
         "Expected '" + golden + "' but got '" + verilog + "'");
  
  deleteContext(c);
}

int main() {
  testBlackboxVerilog();
}
