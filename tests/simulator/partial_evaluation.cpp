#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  TEST_CASE("Partial evaluation") {
    Context* c = newContext();

    SECTION("Partially evaluating a register") {
      uint width = 16;

      Type* regOut =
        c->Record({{"clk", c->Named("coreir.clkIn")},
              {"in", c->BitIn()->Arr(width)},
                {"out", c->Bit()->Arr(width)}});


      REQUIRE(false);
    }

    deleteContext(c);
  }
}
