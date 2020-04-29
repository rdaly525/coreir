#include "add4.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  create_adder(c, 16);
  auto pm = c->getPassManager();

  bool modified = c->runPasses({"coreirjson"});
  assert(modified == false);
  assert(pm->isAnalysisCached("coreirjson") == true);

  modified = c->runPasses({"coreirjson"});
  assert(modified == false);
  assert(pm->isAnalysisCached("coreirjson") == true);

  modified = c->runPasses({"markdirty"});
  assert(modified == true);
  assert(pm->isAnalysisCached("coreirjson") == false);

  modified = c->runPasses({"coreirjson"});
  assert(modified == false);
  assert(pm->isAnalysisCached("coreirjson") == true);
  return 0;
}
