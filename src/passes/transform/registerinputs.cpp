#include "coreir/passes/transform/registerinputs.h"

using namespace std;
using namespace CoreIR;

bool Passes::RegisterInputs::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Module* module = node.getModule();
  if (!module->hasDef()) {
    return false;
  }

  ModuleDef* def = module->getDef();

  Wireable* self = def->sel("self");

  map<Wireable*, Instance*> newRegs;

  Context* c = module->getDef()->getContext();

  for (auto& field : module->getType()->getRecord()) {
    if (field.second != c->Named("coreir.clkIn")) {

      Type::DirKind dk = field.second->getDir();

      if (dk == Type::DirKind::DK_In) {
        //Wireable* w = field.first;
        cout << "Input = " << field.first << endl;
        auto sel = self->sel(field.first);

        Type* selTp = sel->getType();

        if (selTp->getKind() == Type::TK_Array) {

          ArrayType* atp = static_cast<CoreIR::ArrayType*>(selTp);
          int len = atp->getLen();

          cout << "Input type   = " << selTp->toString() << endl;
          cout << "Array length = " << len << endl;

          // TODO: Ensure truly unique name
          auto selReg = def->addInstance(field.first + "_auto_reg",
                                         "coreir.reg",
                                         {{"width", Const::make(c, len)}});

          newRegs.insert({sel, selReg});
        } else {
          // Add a flip flop in front of single bit inputs
          assert(selTp->getKind() == Type::TK_Bit);

          auto selDFF = def->addInstance(field.first + "_auto_dff",
                                         "corebit.dff");
          newRegs.insert({sel, selDFF});
        }

        // cout << "With connections" << endl;
        // for (auto& connected : w->getConnectedWireables()) {
        //   cout << connected->toString() << endl;
        // }
      }
    }
  }

  auto interface = def->getInterface();
  cout << interface->getType()->toString() << endl;

  cout << "# of wireables connected to interfaces = " << interface->getConnectedWireables().size() << endl;
  for (auto& wd : interface->getConnectedWireables()) {
    cout << wd->toString() << endl;
  }

  cout << "# of wireables connected to self = " << self->getConnectedWireables().size() << endl;
  for (auto& wd : self->getConnectedWireables()) {
    cout << wd->toString() << endl;
  }

  for (auto& conn : def->getConnections()) {
    cout << Connection2Str(conn) << " ";

    
    Wireable* sel1 = conn.first;
    Wireable* sel2 = conn.second;

    Wireable* inSel;
    Wireable* outSel;

    bool foundIn = false;

    if (newRegs.find(sel1) != std::end(newRegs)) {
      foundIn = true;
      inSel = sel1;
      outSel = sel2;
      cout << "Contains input " << endl;
    }

    if (newRegs.find(sel2) != std::end(newRegs)) {
      foundIn = true;
      inSel = sel2;
      outSel = sel1;
      cout << "Contains input " << endl;
    }
    
    cout << endl;

    if (foundIn) {

      def->disconnect(conn);
      def->connect(outSel, newRegs[inSel]->sel("out"));

    }
  }

  for (auto& selPair : newRegs) {
    def->connect(selPair.first, (selPair.second)->sel("in"));
  }
  
  return true;
}
