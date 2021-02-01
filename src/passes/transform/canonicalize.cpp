#include "coreir/passes/transform/canonicalize.h"
#include "coreir/ir/types.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"

namespace IR = CoreIR;
namespace {

// This will make sure to combine all the
void handle_input_port(IR::Wireable* w) {
  ASSERT(w->getType()->isInput(), "Expecting type to be input");
  auto c = w->getContext();
  if (w->getSelects().size() == 0) { return; }
  auto def = w->getContainer();
  auto pack = def->addInstance("_pack" + c->getUnique(), "coreir.pack", {{"type", IR::Const::make(c, w->getType()->getFlipped())}});
  w->connect(pack->sel("out"));
  bool is_array = IR::isa<IR::ArrayType>(w->getType());
  for (auto &[field, sub_w]: w->getSelects() ) {
    //Arrays have input ports _0, _1, _2, etc...
    std::string f = field;
    if (is_array) { f = "_" + field;}
    auto unpack_sub_w = pack->sel(f);
    sub_w->reconnect(unpack_sub_w);
    handle_input_port(unpack_sub_w);
  }
}

void handle_output_port(IR::Wireable* w) {
  ASSERT(w->getType()->isOutput(), "Expecting type to be output");
  auto c = w->getContext();
  if (w->getSelects().size() == 0) { return; }
  auto def = w->getContainer();
  auto unpack = def->addInstance("_unpack" + c->getUnique(), "coreir.unpack", {{"type", IR::Const::make(c, w->getType())}});
  w->connect(unpack->sel("in"));
  bool is_array = IR::isa<IR::ArrayType>(w->getType());
  for (auto &[field, sub_w]: w->getSelects() ) {
    //Arrays have output ports _0, _1, _2, etc...
    std::string f = field;
    if (is_array) { f = "_" + field;}
    auto unpack_sub_w = unpack->sel(f);
    sub_w->reconnect(unpack_sub_w);
    handle_output_port(unpack_sub_w);
  }
}

}  // namespace

namespace CoreIR {
namespace Passes {

//Goal, anytime there is a layer with a select path
bool Canonicalize::runOnModule(Module* m) {
  // Find the clock gating pattern (a register driving a mux driving the
  // register)
  if (!m->hasDef()) { return false; }
  auto def = m->getDef();

  //Initially just verify that the inputs are of the appropriate form
  for (auto &[iname, inst]: def->getInstances(true)) {
    for (auto &[pname, ptype]: dyn_cast<RecordType>(inst->getType())->getRecord()) {
      if (ptype->isInput()) { handle_input_port(inst->sel(pname)); }
    }
  }

  //Actually Fix up the output ports
  for (auto &[iname, inst]: def->getInstances(true)) {
    for (auto &[pname, ptype]: dyn_cast<RecordType>(inst->getType())->getRecord()) {
      if (ptype->isOutput()) { handle_output_port(inst->sel(pname)); }
    }
  }
  return false;


}  // runOnModule
}  // namespace Passes
}  // namespace IR
