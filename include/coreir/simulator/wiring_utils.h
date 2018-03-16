#pragma once

#include "coreir/ir/module.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/wireable.h"
#include "coreir/simulator/algorithm.h"

namespace CoreIR {

  CoreIR::Wireable* replaceSelect(CoreIR::Wireable* const toReplace,
                                  CoreIR::Wireable* const replacement,
                                  CoreIR::Wireable* const sel);

  std::vector<Connection>
  getReceiverConnections(CoreIR::Wireable* w);

  std::vector<Connection>
  getSourceConnections(CoreIR::Wireable* w);

  std::vector<Select*>
  getReceiverSelects(CoreIR::Wireable* inst);

  std::vector<Select*>
  getSourceSelects(CoreIR::Wireable* inst);

  std::vector<Select*>
  getIOSelects(CoreIR::Wireable* inst);
  
  std::map<Wireable*, Wireable*>
  signalDriverMap(CoreIR::ModuleDef* const def);

  std::map<Wireable*, std::vector<Wireable*> >
  signalReceiverMap(CoreIR::ModuleDef* const def);
  
  bool isAncestorOf(Wireable* const possibleAncestor,
                    Wireable* const w);

  std::vector<Wireable*>
  drivenBy(Wireable* const w,
           std::map<Wireable*, std::vector<Wireable*> >& receiverMap);

  std::vector<CoreIR::Select*>
  getSignalValues(CoreIR::Select* const sel);

  maybe<BitVector>
  getSignalBitVec(const std::vector<CoreIR::Select*>& signals);

  std::vector<Connection>
  unpackConnection(const CoreIR::Connection& conn);

  void portToConstant(const std::string& portName,
                      const BitVector& value,
                      CoreIR::Module* const mod);

  void setRegisterInit(const std::string& instanceName,
                       const BitVector& value,
                       CoreIR::Module* const mod);

  bool isBitType(const Type& tp);
}
