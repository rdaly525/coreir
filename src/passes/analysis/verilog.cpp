#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/passes/analysis/verilog.h"

using namespace std;

namespace CoreIR {

std::string Passes::Verilog::ID = "verilog";
bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  
  //Create a new Vmodule for this node
  Module* m = node.getModule();
  
  vmods.addModule(m);
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  
  if (vmods.externalVMods.size() > 0) {
    os << "/* External Modules" << endl;
    for (auto ext : vmods.externalVMods) {
      os << ext->toString() << endl << endl;
    }
    os << "*/" << endl << endl;
  }
  for (auto vmod : vmods.vmods) {
    cout << "doing: " << vmod->modname << endl;
    if (vmod->isExternal) {
      continue;
    }
    os << vmod->toString() << endl;
  }

}

Passes::Verilog::~Verilog() {
  //set<VModule*> toDelete;
  //for (auto m : modMap) {
  //  toDelete.insert(m.second);
  //}
  //for (auto m : toDelete) {
  //  delete m;
  //}
}

}
