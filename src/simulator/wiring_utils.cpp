#include "coreir/simulator/wiring_utils.h"

#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/dynamic_bit_vector.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/op_graph.h"
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

  std::vector<Select*>
  getSourceSelects(CoreIR::Wireable* inst) {
    vector<Select*> conns;

    for (auto sel : inst->getConnectedWireables()) {
      if (sel->getType()->getDir() == Type::DK_Out) {
        conns.push_back(cast<Select>(sel));
      }
    }

    for (auto sel : inst->getSelects()) {
      concat(conns, getSourceSelects(sel.second));
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

  CoreIR::Select* getDriverSelect(CoreIR::Select* const src) {
    // Outputs do not have drivers
    assert(src->getType()->getDir() == Type::DK_In);
    //assert(src->getType()->getKind() == Type::TK_BitIn);

    auto connected = src->getConnectedWireables();
    // No direct connections
    if (connected.size() == 0) {

      //cout << src->toString() << " has no direct connections" << endl;

      Wireable* parent = src->getParent();
      if (!isa<Select>(parent)) {
        cout << "Need to implement lower type hierarchy search" << endl;
        assert(false);
      }

      Select* parentSel = cast<Select>(parent);
      Select* parentDriver = getDriverSelect(parentSel);

      if (parentDriver == nullptr) {
        return nullptr;
      }

      Select* res = parentDriver->sel(src->getSelStr());

      //cout << src->toString() << " has no direct connections" <<
      //" is driven by " << res->toString() << endl;

      return res;
    }

    assert(connected.size() == 1);

    return cast<Select>(*std::begin(connected));
  }

  std::vector<CoreIR::Select*>
  getSignalValues(CoreIR::Select* const sel) {
    assert(isBitArray(*(sel->getType())));

    ArrayType* tp = cast<ArrayType>(sel->getType());

    uint len = tp->getLen();
    Type* elemType = tp->getElemType();

    assert(elemType->getDir() == Type::DK_In);

    vector<Select*> sels;
    for (uint i = 0; i < len; i++) {
      Select* inSel = sel->sel(to_string(i));
      Select* driverSel = getDriverSelect(inSel);

      sels.push_back(driverSel);
    }

    return sels;
  }

  maybe<BitVector>
  getSignalBitVec(const std::vector<CoreIR::Select*>& signals) {

    BitVector bv(signals.size(), 0);

    // cout << "Getting signal bit vec" << endl;
    // for (auto sig : signals) {
    //   cout << "\t" << sig << endl;
    // }

    for (uint i = 0; i < ((uint) bv.bitLength()); i++) {
      //cout << "Getting signal " << i << endl;
      Select* sigi = signals[i];

      if (sigi == nullptr) {
        return maybe<BitVector>();
      }

      //cout << "sigi = " << sigi->toString() << endl;

      Wireable* src = extractSource(sigi);

      if (!isConstant(src)) {
        return maybe<BitVector>();
      }

      Instance* srcConst = cast<Instance>(src);
      if (getQualifiedOpName(*srcConst) == "corebit.const") {
        bool val = srcConst->getModArgs().at("value")->get<bool>();
        if (val == true) {
          bv.set(i, 1);
        } else {
          bv.set(i, 0);
        }
      } else {
        ASSERT(getQualifiedOpName(*srcConst) == "coreir.const",
               "must be constant");

        BitVector val = srcConst->getModArgs().at("value")->get<BitVector>();
        bv.set(i, val.get(i));
      }
    }

    return maybe<BitVector>(bv);
  }

  std::vector<Connection>
  unpackConnection(const CoreIR::Connection& conn) {
    Wireable* fst = conn.first;
    Wireable* snd = conn.second;

    assert(fst->getType() == snd->getType()->getFlipped());

    Type* fstType = fst->getType();

    // Bit connections are already unpacked
    if ((fstType->getKind() == Type::TK_Bit) ||
        (fstType->getKind() == Type::TK_BitIn)) {
      return {conn};
    }

    if (fstType->getKind() == Type::TK_Named) {
      return {conn};
    }

    vector<Connection> unpackedConns;

    if (fstType->getKind() == Type::TK_Array) {
      ArrayType* arrTp = cast<ArrayType>(fstType);
      int len = arrTp->getLen();

      for (int i = 0; i < len; i++) {
        concat(unpackedConns, unpackConnection({fst->sel(i), snd->sel(i)}));
      }

      return unpackedConns;

    } else {
      cout << "Wireable " << fst->toString() << " has unsupported type in unpackConnection = " << fstType->toString() << endl;
      assert(false);
    }

    assert(false);
  }

}
