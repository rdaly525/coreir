#include "coreir.h"
#include "coreir/passes/transform/clockifyinterface.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 8;

  Type* clType = c->Record({
      {"clk", c->BitIn()},
        {"in", c->BitIn()->Arr(width)}
    });

  CoreIRLoadLibrary_rtlil(c);

  deleteContext(c);
}
