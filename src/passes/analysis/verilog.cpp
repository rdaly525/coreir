#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/passes/analysis/verilog.h"

using namespace std;
using namespace CoreIR;
using namespace CoreIR::Passes;

namespace {

//string VWireDec(VWire w) { return "  wire " + w.dimstr() + " " + w.getName() + ";"; }
//
//
//string VAssign(Connection con) {
//  Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
//  Wireable* right = left==con.first ? con.second : con.first;
//  VWire vleft(left);
//  VWire vright(right);
//  return "  assign " + vleft.getName() + vleft.dimstr() + " = " + vright.getName() + vright.dimstr() + ";";
//}
//
//}

std::string Passes::Verilog::ID = "verilog";
bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  
  //Create a new Vmodule for this node
  Module* m = node.getModule();
  
  vmods->addModule(m);
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  
  for (auto ext : vmods.externalVMods) {
    os << "// " << ext->modname << " defined externally!" << endl;
  }
  os << endl;
  for (auto vmod : vmods.vmods) {
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
