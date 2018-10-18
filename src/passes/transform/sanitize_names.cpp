#include "coreir.h"
#include "coreir/passes/transform/sanitize_names.h"

using namespace std;
using namespace CoreIR;

string Passes::SanitizeNames::ID = "sanitize-names";

std::string sanitizedName(const std::string& cellName) {
  string instName = "";
  for (uint i = 0; i < cellName.size(); i++) {
    if (cellName[i] == '$') {
      //instName += "UDOLLARU";
    } else if (cellName[i] == ':') {
      //instName += "UCOLONU";
    } else if (cellName[i] == '.') {
      //instName += "UDOTU";
    } else if (cellName[i] == '\\') {
      instName += "UBACKSLASHU";
    } else if (cellName[i] == '=') {
      instName += "UEQUALSU";
    } else if (cellName[i] == '[') {
      instName += "ULEFTUBRACKETU";
    } else if (cellName[i] == ']') {
      instName += "URIGHTUBRACKETU";
    } else if (cellName[i] == '/') {
      instName += "UFORWARDUSLASHU";
    } else if (cellName[i] == '_') {
      //instName += "UUNDERSCOREU";
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

  cout << "Sanitizing names in " << m->getName() << endl;
  set<Instance*> allInstances;
  for (auto inst : def->getInstances()) {
    allInstances.insert(inst.second);
  }

  while (allInstances.size() > 0) {
    Instance* inst = *begin(allInstances);
    allInstances.erase(inst);

    string sName = sanitizedName(inst->getInstname());

    if (sName != inst->getInstname()) {
      Instance* instPT = addPassthrough(inst, "_sanitize_names_PT");

      auto sels = inst->getSelects();

      inst->disconnectAll();

      auto safeNameInstance =
        def->addInstance(inst, sName);

      for (auto selR : sels) {
        def->connect(instPT->sel("in")->sel(selR.first),
                     safeNameInstance->sel(selR.first));
      }

      def->removeInstance(inst);

      inlineInstance(instPT);
    }
  }

  return changedName;
}
