#include "coreir.h"
#include "coreir/passes/analysis/smvmodule.hpp"
#include "coreir/passes/analysis/smv.h"

using namespace CoreIR;
using namespace Passes;

namespace {

  string CLOCK = "clk";
  
  std::vector<string> check_interface_variable(std::vector<string> variables, SmvBVVar var, SMVModule* smod) {
  if ( find(variables.begin(), variables.end(), var.getName()) == variables.end() ) {
      variables.push_back(var.getName());
      smod->addVarDec(SmvBVVarDec(SmvBVVarGetCurr(var)));
      if (var.getName().find(CLOCK) != string::npos) {
        smod->addStmt("-- START module declaration for signal '" + var.getName() + "'");
        smod->addStmt(SMVClock("", var));
        smod->addStmt("-- END module declaration\n");
      }
    }
  return variables;
  }

}

std::string Passes::SMV::ID = "smv";
bool Passes::SMV::runOnInstanceGraphNode(InstanceGraphNode& node) {

  //Create a new SMVmodule for this node
  Module* m = node.getModule();
  SMVModule* smod = new SMVModule(m);
  modMap[m] = smod;
  if (!m->hasDef()) {
    return false;
  }

  if (this->getContext()->hasTop() &&
      this->getContext()->getTop()->getMetaData().count("properties") > 0) {
    json jprop = this->getContext()->getTop()->getMetaData()["properties"];
    if (jprop.size()) {
      for (uint i=0; i<jprop.size(); i++) {
        string propname = jprop[i][0];
        PropType ptype = jprop[i][1] == "invar" ? invarspec : ltlspec;
        string propval = jprop[i][2];
        PropDef prop = make_pair(ptype, propval);
        properties.emplace(propname, prop);
      }
    }
  }
  
  ModuleDef* def = m->getDef();

  static std::vector<string> variables; 
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Module* mref = imap.second->getModuleRef();
    // do not add comment for no ops
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt("-- START module declaration for instance '" + imap.first + "' (Module "+ mref->getName() + ")");
    }
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      SmvBVVar var = SmvBVVar(iname, rmap.first, rmap.second);
      smod->instantiate();
      smod->addPort(var);
      variables.push_back(var.getName());
      smod->addVarDec(SmvBVVarDec(SmvBVVarGetCurr(var)));
    }
    ASSERT(modMap.count(mref),"DEBUG ME: Missing mref");
    smod->addStmt(modMap[mref]->toInstanceString(inst, imap.first));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt("-- END module declaration\n");
    }
  }

  smod->addStmt("-- START connections definition");
  for (auto con : def->getConnections()) {
    Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
    Wireable* right = left==con.first ? con.second : con.first;

    SmvBVVar vleft, vright;
    
    if (isNumber(left->getSelectPath().back())) {
      auto lsel = dyn_cast<Select>(left)->getParent();
      vleft = SmvBVVar(lsel);
    } else {
      vleft = SmvBVVar(left);
    }

    if (isNumber(right->getSelectPath().back())) {
      auto rsel = dyn_cast<Select>(right)->getParent();
      vright = SmvBVVar(rsel);
    } else {
      vright = SmvBVVar(right);
    }
    
    variables = check_interface_variable(variables, vleft, smod);
    variables = check_interface_variable(variables, vright, smod);

    SmvBVVar lleft(left);
    SmvBVVar lright(right);
    
    smod->addStmt(SMVAssign(lleft, lright));
  }
  smod->addStmt("-- END connections definition\n");

  return false;
}

void Passes::SMV::writeToStream(std::ostream& os) {

  os << "#define B(bv) (bv = 0ud1_1)" << endl;
  
  os << "MODULE main" << endl;
  
  os << "-- Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0 && mmap.second->isInstantiated()) {
      os << mmap.second->toVarDecString() << endl;
    }
  }

  os << "-- Modules definitions" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0 && mmap.second->isInstantiated()) {
      os << mmap.second->toString() << endl;
    }
  }

  os << "-- Properties" << endl;
  for (auto property : properties) {
    os << SMVProperty(property.first, property.second.first, property.second.second) << endl;
  }

}
