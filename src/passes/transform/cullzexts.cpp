#include "coreir.h"
#include "coreir/passes/transform/cullzexts.h"

using namespace std;
using namespace CoreIR;

string Passes::CullZexts::ID = "cullzexts";

bool Passes::CullZexts::runOnModule(Module* m) {
  return false;
}
