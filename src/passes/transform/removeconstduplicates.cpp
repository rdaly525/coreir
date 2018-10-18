#include "coreir/passes/transform/removeconstduplicates.h"

using namespace std;
using namespace CoreIR;

namespace CoreIR {

  namespace Passes {

    string Passes::RemoveConstDuplicates::ID = "removeconstduplicates";
    bool RemoveConstDuplicates::runOnModule(Module* m) {
      if (!m->hasDef()) {
        return false;
      }

      cout << "Processing module " << m->getName() << endl;

      vector<Instance*> bitConstZeros;
      vector<Instance*> bitConstOnes;

      ModuleDef* def = m->getDef();
      for (auto instR : def->getInstances()) {
        auto inst = instR.second;

        if (getQualifiedOpName(*inst) == "corebit.const") {
          bool val = inst->getModArgs().at("value")->get<bool>();
          if (val == true) {
            bitConstOnes.push_back(inst);
          } else {
            bitConstZeros.push_back(inst);
          }
        }
      }

      cout << "# of zero bit consts = " << bitConstZeros.size() << endl;
      cout << "# of one bit consts  = " << bitConstOnes.size() << endl;

      bool changed = false;
      if ((bitConstZeros.size() > 1)) {
        cout << "Removing duplicate zero bitconsts " << endl;

        Instance* zC = bitConstZeros.back();
        bitConstZeros.pop_back();

        vector<Connection> newConns;
        for (auto zeroConst : bitConstZeros) {

          for (auto conn : getReceiverConnections(zeroConst)) {
            Wireable* fst = conn.first;
            Wireable* snd = conn.second;

            Wireable* newFst = replaceSelect(zeroConst->sel("out"),
                                             zC->sel("out"),
                                             fst);

            Wireable* newSnd = replaceSelect(zeroConst->sel("out"),
                                             zC->sel("out"),
                                             snd);

            newConns.push_back({newFst, newSnd});

          }
          def->removeInstance(zeroConst);
        }

        for (auto conn : newConns) {
          def->connect(conn.first, conn.second);
        }

        changed = true;
      }

      if ((bitConstOnes.size() > 1)) {
        cout << "Removing duplicate one bitconsts " << endl;

        Instance* zC = bitConstOnes.back();
        bitConstOnes.pop_back();

        vector<Connection> newConns;
        for (auto zeroConst : bitConstOnes) {

          for (auto conn : getReceiverConnections(zeroConst)) {
            Wireable* fst = conn.first;
            Wireable* snd = conn.second;

            Wireable* newFst = replaceSelect(zeroConst->sel("out"),
                                             zC->sel("out"),
                                             fst);

            Wireable* newSnd = replaceSelect(zeroConst->sel("out"),
                                             zC->sel("out"),
                                             snd);

            newConns.push_back({newFst, newSnd});

          }
          def->removeInstance(zeroConst);
        }

        for (auto conn : newConns) {
          def->connect(conn.first, conn.second);
        }

        changed = true;
      }

      cout << "Done with bitconst removal" << endl;

      return changed;
    }
  }
}
