#include "coreir.h"
#include "coreir/passes/transform/groupconnections.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::GroupConnections::ID = "groupconnections";
bool Passes::GroupConnections::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  return false;
}
