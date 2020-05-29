#include "passes/analysis/printer.h"
#include "ir/coreir.h"
#include "passes/analysis/coreirjson.h"

using namespace std;
using namespace CoreIR;

string Passes::Printer::ID = "printer";
bool Passes::Printer::runOnContext(Context* c) {
  cout << "Printer!\n";
  if (c->hasTop()) {
    getAnalysisPass<Passes::CoreIRJson>()->writeToStream(
      cout,
      c->getTop()->getRefName());
  }
  else {
    getAnalysisPass<Passes::CoreIRJson>()->writeToStream(cout);
  }
  cout << endl << endl;
  return false;
}
