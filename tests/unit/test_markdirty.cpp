#include "coreir.h"
#include "add4.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext()
  Module* add4 = create_adder(c,n);
  auto pm = c->getPassManager();
  
  bool modified = c->runPasses("coreirjson");
  assert(modified==false);
  assert(pm->isAnalysisCached("coreirjson")==true);
  
  modified = c->runPasses("coreirjson");
  assert(modified==false);
  assert(pm->isAnalysisCached("coreirjson")==true);
  
  modified = c->runPasses("markdirty");
  assert(modified==true);
  assert(pm->isAnalysisCached("coreirjson")==false);

  modified = c->runPasses("coreirjson");
  assert(modified==false);
  assert(pm->isAnalysisCached("coreirjson")==true);

