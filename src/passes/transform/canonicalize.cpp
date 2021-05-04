#include "coreir/common/unused.hpp"
#include "coreir/passes/transform/canonicalize.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/types.h"

using namespace CoreIR;
namespace {


void handleInputPort(CoreIR::Wireable* wireable) {
  ASSERT(wireable->getType()->isInput(), "Expecting type to be input");
  auto context = wireable->getContext();
  if (wireable->getSelects().size() == 0) return;
  auto def = wireable->getContainer();
  auto t = wireable->getType();
  if (isBit(t)) {
    return;
  }
  if (isBitVector(t)) {
    // wireable has connections off of a bitvector. Need an unpack node
    auto pack = def->addInstance(
      "_pack" + context->getUnique(),
      "coreir.pack",
      {{"type",
        CoreIR::Const::make(context, wireable->getType()->getFlipped())}});
    wireable->connect(pack->sel("out"));
    for (auto& [field, sub_wireable] : wireable->getSelects()) {
      handleInputPort(sub_wireable);
    }
  }
  else {
    ASSERT(isa<ArrayType>(t) || isa<RecordType>(t), "NYI");
    for (auto &[field, sub_wireable]: wireable->getSelects() ) {
      handleInputPort(sub_wireable);
    }
  }
}

void handleOutputPort(CoreIR::Wireable* wireable) {
  ASSERT(wireable->getType()->isOutput(), "Expecting type to be output");
  auto context = wireable->getContext();
  if (wireable->getSelects().size() == 0) return;
  auto def = wireable->getContainer();
  auto unpack = def->addInstance(
      "_unpack" + context->getUnique(),
      "coreir.unpack",
      {{"type", CoreIR::Const::make(context, wireable->getType())}});
  wireable->connect(unpack->sel("in"));
  bool is_array = CoreIR::isa<CoreIR::ArrayType>(wireable->getType());
  for (auto &[field, sub_wireable]: wireable->getSelects() ) {
    // Arrays have output ports _0, _1, _2, etc...
    std::string f = field;
    if (is_array) f = "_" + field;
    auto unpack_sub_wireable = unpack->sel(f);
    sub_wireable->reconnect(unpack_sub_wireable);
    handleOutputPort(unpack_sub_wireable);
  }
}

}  // namespace

namespace CoreIR {
namespace Passes {

bool Canonicalize::runOnModule(Module* m) {
  if (!m->hasDef()) return false;

  auto def = m->getDef();

  // Initially just enforce that the inputs are of the appropriate form.
  for (auto &[iname, inst] : def->getWireables(true)) {
    ::common::unused(iname);
    for (auto &[pname, ptype] : dyn_cast<RecordType>(inst->getType())->getRecord()) {
      if (ptype->isInput()) handleInputPort(inst->sel(pname));
    }
  }

  // Actually fix up the output ports.
  for (auto &[iname, inst] : def->getWireables(true)) {
    ::common::unused(iname);
    for (auto &[pname, ptype] : dyn_cast<RecordType>(inst->getType())->getRecord()) {
      if (ptype->isOutput()) handleOutputPort(inst->sel(pname));
    }
  }

  return false;
}

}  // namespace Passes
}  // namespace CoreIR
