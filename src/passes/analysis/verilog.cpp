#include "coreir.h"
#include "coreir-passes/analysis/verilog.h"

using namespace CoreIR;

std::string Passes::Verilog::ID = "verilog";
bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  cout << "NYI: Running Verilog" << endl;
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  ASSERT(0,"NYI");
}
