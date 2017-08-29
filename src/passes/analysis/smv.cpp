#include "coreir.h"
#include "coreir-passes/analysis/smvmodule.hpp"
#include "coreir-passes/analysis/smv.h"

using namespace CoreIR;
using namespace Passes;

namespace {

  string CLOCK = "clk";
  
  std::vector<string> check_interface_variable(std::vector<string> variables, SmvBVVar var, SMVModule* smod) {
  if ( find(variables.begin(), variables.end(), var.getName()) == variables.end() ) {
      variables.push_back(var.getName());
      smod->addVarDec(SmvBVVarDec(SmvBVVarGetCurr(var)));
      // smod->addStmt("-- ADDING missing variable: " +var.getName()+"\n");
      if (var.getName().find(CLOCK) != string::npos) {
        smod->addStmt("-- START module declaration for signal '" + var.getName());
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
  Instantiable* i = node.getInstantiable();
  if (auto g = dyn_cast<Generator>(i)) {
    this->modMap[i] = new SMVModule(g);
    this->external.insert(i);
    return false;
  }
  Module* m = cast<Module>(i);
  SMVModule* smod = new SMVModule(m);
  modMap[i] = smod;
  if (!m->hasDef()) {
    this->external.insert(i);
    return false;
  }

  ModuleDef* def = m->getDef();

  static std::vector<string> variables; 
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Instantiable* iref = imap.second->getInstantiableRef();
    // do not add comment for no ops
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt("-- START module declaration for instance '" + imap.first + "' (Module "+ iref->getName() + ")");
    }
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      SmvBVVar var = SmvBVVar(iname, rmap.first, rmap.second);
      smod->addPort(var);
      variables.push_back(var.getName());
      smod->addVarDec(SmvBVVarDec(SmvBVVarGetCurr(var)));
    }
    ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");
    smod->addStmt(modMap[iref]->toInstanceString(inst, imap.first));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt("-- END module declaration\n");
    }
  }

  json& jprop = m->getProperty();

  if (jprop.size()) {
    for (int i=0; i<jprop.size(); i++) {
      string propname = jprop[i][0];
      PropType ptype = jprop[i][1] == "invar" ? invarspec : ltlspec;
      string propval = jprop[i][2];
      PropDef prop = make_pair(ptype, propval);
      properties.emplace(propname, prop);
    }
  }

  smod->addStmt("-- START connections definition");
  for (auto con : def->getConnections()) {
    Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
    Wireable* right = left==con.first ? con.second : con.first;
    SmvBVVar vleft(left);
    SmvBVVar vright(right);

    variables = check_interface_variable(variables, vleft, smod);
    variables = check_interface_variable(variables, vright, smod);
    
    smod->addStmt(SMVAssign(vleft, vright));
  }
  smod->addStmt("-- END connections definition\n");

  return false;
}

void Passes::SMV::writeToStream(std::ostream& os) {

  os << "MODULE main" << endl;
  
  // Print variable declarations
  
  os << "-- Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toVarDecString() << endl;
    }
  }

  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toString() << endl;
    }
  }

  for (auto property : properties) {
    os << SMVProperty(property.first, property.second.first, property.second.second) << endl;
  }

}
