#include "coreir.h"
#include "assert_pass.h"

using namespace CoreIR;

void testIce40Verilog(const char* json, const char* verilog) {
  Context* c = newContext();
  c->getLibraryManager()->loadLib("ice40");

  Module* top;
  if (!loadFromFile(c, json, &top)) {
    c->printerrors();
  }
  assert(top);

  c->runPasses({"verilog"});

  assertPassEq<Passes::Verilog>(c, verilog);

  deleteContext(c);
}

int main() {
  testIce40Verilog("gold/ice40_pll.json", "gold/ice40_pll_verilog.v");
  testIce40Verilog("gold/ice40_ram.json", "gold/ice40_ram_verilog.v");
  return 0;
}
