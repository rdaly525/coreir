#include "coreir.h"
#include "coreir/passes/transform/sanitize_names.h"

using namespace std;
using namespace CoreIR;

string Passes::SanitizeNames::ID = "sanitize-names";

std::string sanitizedName(const std::string& cellName) {
  string instName = "";
  for (uint i = 0; i < cellName.size(); i++) {
    if (cellName[i] == '$') {
      instName += "__DOLLAR__";
    } else if (cellName[i] == ':') {
      instName += "__COLON__";
    } else if (cellName[i] == '.') {
      instName += "__DOT__";
    } else if (cellName[i] == '\\') {
      instName += "__BACKSLASH__";
    } else if (cellName[i] == '=') {
      instName += "__EQUALS__";
    } else if (cellName[i] == '[') {
      instName += "__LEFT_BRACKET__";
    } else if (cellName[i] == ']') {
      instName += "__RIGHT_BRACKET__";
    } else if (cellName[i] == '/') {
      instName += "__FORWARD_SLASH__";
    } else {
      instName += cellName[i];
    }

  }

  return instName;
  
}

bool Passes::SanitizeNames::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  bool changedName = false;

  auto def = m->getDef();

  set<Instance*> allInstances;
  for (auto inst : def->getInstances()) {
    allInstances.insert(inst.second);
  }

  while (allInstances.size() > 0) {
    Instance* inst = *begin(allInstances);
    allInstances.erase(inst);

    Instance* instPT = addPassthrough(inst, "_sanitize_names_PT");

    auto sels = inst->getSelects();

    inst->disconnectAll();

    string sName = sanitizedName(inst->getInstname());

    auto safeNameInstance =
      def->addInstance(inst, sName);

    for (auto selR : sels) {
      def->connect(instPT->sel("in")->sel(selR.first),
                   safeNameInstance->sel(selR.first));
    }

    def->removeInstance(inst);

    inlineInstance(instPT);
  }

  return changedName;
}
