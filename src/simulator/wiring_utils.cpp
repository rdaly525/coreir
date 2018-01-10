#include "coreir/simulator/wiring_utils.h"

#include "coreir/ir/types.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/utils.h"

using namespace std;

namespace CoreIR {

  CoreIR::Wireable* replaceSelect(CoreIR::Wireable* const toReplace,
                                  CoreIR::Wireable* const replacement,
                                  CoreIR::Wireable* const sel) {
    if (toReplace == sel) {
      return replacement;
    }

    if (isa<Select>(sel)) {
      Select* selP = cast<Select>(sel);
      return replaceSelect(toReplace,
                           replacement,
                           selP->getParent())->sel(selP->getSelStr());
    }

    return sel;
  }

  std::vector<Connection>
  getReceiverConnections(CoreIR::Wireable* w) {
    vector<Connection> conns;

    for (auto sel : w->getConnectedWireables()) {
      if (sel->getType()->getDir() == Type::DK_In) {
        conns.push_back({sel, w});
      }
    }

    for (auto sel : w->getSelects()) {
      concat(conns, getReceiverConnections(sel.second));
    }

    return conns;
  }

  std::vector<Connection>
  getSourceConnections(CoreIR::Wireable* w) {
    vector<Connection> conns;

    for (auto sel : w->getConnectedWireables()) {
      if (sel->getType()->getDir() == Type::DK_Out) {
        conns.push_back({sel, w});
      }
    }

    for (auto sel : w->getSelects()) {
      concat(conns, getSourceConnections(sel.second));
    }

    return conns;
  }
  
  std::vector<Select*>
  getReceiverSelects(CoreIR::Wireable* inst) {
    vector<Select*> conns;

    for (auto sel : inst->getConnectedWireables()) {
      if (sel->getType()->getDir() == Type::DK_In) {
        conns.push_back(cast<Select>(sel));
      }
    }

    for (auto sel : inst->getSelects()) {
      concat(conns, getReceiverSelects(sel.second));
    }

    return conns;
  }

  std::map<Wireable*, Wireable*> signalDriverMap(CoreIR::ModuleDef* const def) {
    map<Wireable*, Wireable*> bitToDriver;

    for (auto connection : def->getConnections()) {
      Wireable* fst = connection.first;
      Wireable* snd = connection.second;

      assert(isSelect(fst));
      assert(isSelect(snd));

      Select* fst_select = static_cast<Select*>(fst);

      Type* fst_tp = fst_select->getType();

      if (fst_tp->isInput()) {
        bitToDriver[fst] = snd;
      } else {
        bitToDriver[snd] = fst;
      }
      
    }
    return bitToDriver;
  }

  std::map<Wireable*, std::vector<Wireable*> >
  signalReceiverMap(CoreIR::ModuleDef* const def) {
    map<Wireable*, vector<Wireable*> > bitToDriver;

    for (auto connection : def->getConnections()) {
      Wireable* fst = connection.first;
      Wireable* snd = connection.second;

      assert(isSelect(fst));
      assert(isSelect(snd));

      Select* fst_select = static_cast<Select*>(fst);

      Type* fst_tp = fst_select->getType();

      if (fst_tp->isInput()) {
        map_insert(bitToDriver, snd, fst);
      } else {
        map_insert(bitToDriver, fst, snd);
      }
      
    }
    return bitToDriver;
  }

  bool isAncestorOf(Wireable* const possibleAncestor,
                    Wireable* const w) {
    if (possibleAncestor == w) {
      return true;
    }

    if (isa<Select>(w)) {
      Select* ws = cast<Select>(w);
      return isAncestorOf(possibleAncestor, ws->getParent());
    }

    return false;
  }

  vector<Wireable*>
  drivenBy(Wireable* const w,
           std::map<Wireable*, std::vector<Wireable*> >& receiverMap) {
    vector<Wireable*> driven;
    for (auto rec : receiverMap) {
      if (isAncestorOf(w, rec.first)) {
        concat(driven, rec.second);
      }
    }
    return driven;
  }
  
}
