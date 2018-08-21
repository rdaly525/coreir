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
  
  cout << "H0" << endl;
  for (auto ext : vmods.externalVMods) {
    os << "// " << ext->modname << " defined externally!" << endl;
  }
  os << endl;
  for (auto vmod : vmods.vmods) {
    cout << "H1" << endl;
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
