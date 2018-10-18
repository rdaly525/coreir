#include "coreir.h"
#include "coreir/passes/transform/cullzexts.h"

using namespace std;
using namespace CoreIR;

string Passes::CullZexts::ID = "cullzexts";

bool noSubSelects(CoreIR::Select* const outSel) {
  if ((outSel->getSelects().size() == 0) &&
      (outSel->getConnectedWireables().size() == 0)) {
    return true;
  }

  for (auto sel : outSel->getSelects()) {
    if (!noSubSelects(sel.second)) {
      return false;
    }
  }

  return true;
}

bool Passes::CullZexts::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  auto def = m->getDef();

  bool deletedZext = false;

  cout << "Deleting zexts in " << m->toString() << endl;
  cout << "# of instance in " << m->toString() << " = " << def->getInstances().size() << endl;

  vector<Instance*> toDelete;
  
  for (auto instS : def->getInstances()) {
    Instance* inst = instS.second;

    if (getQualifiedOpName(*inst) == "coreir.zext") {
      auto args = inst->getModuleRef()->getGenArgs();

      uint in_width = args.at("width_in")->get<int>();
      uint out_width = args.at("width_out")->get<int>();

      if (in_width == out_width) {

        //cout << inst->toString() << " is an identity zext" << endl;

        toDelete.push_back(inst);
      }
    }
  }

  cout << "Deleting " << toDelete.size() << " id zexts" << endl;
  deletedZext = toDelete.size() > 0;

  for (auto inst : toDelete) {

    Instance* instPT = addPassthrough(inst, "_cullZext_PT");

    def->removeInstance(inst);

    def->connect(instPT->sel("in")->sel("in"),
                 instPT->sel("in")->sel("out"));

    inlineInstance(instPT);
  }

  cout << "Done culling zero extends" << endl;

  return deletedZext;
}
