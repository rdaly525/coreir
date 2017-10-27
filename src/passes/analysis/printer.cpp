#include "coreir.h"
#include "coreir/passes/analysis/printer.h"
#include "coreir/passes/analysis/coreirjson.h"

using namespace std;
using namespace CoreIR;

string Passes::Printer::ID = "printer";
bool Passes::Printer::runOnContext(Context* c) {
  cout << "Printer!\n";
  getAnalysisPass<Passes::CoreIRJson>()->writeToStream(cout,c->getTop()->getRefName());
  cout << endl << endl;
  return false;
}

