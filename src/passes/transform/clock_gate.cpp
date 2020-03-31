#include "coreir/passes/transform/clock_gate.h"

std::string CoreIR::Passes::ClockGate::ID = "clock_gate";

namespace {
struct CEInfo {
  bool can_replace = false;
  CoreIR::Instance *reg = nullptr;
  CoreIR::Instance *mux = nullptr;
  int mux_in_port = 0;
  CEInfo() : can_replace(false) {}
  CEInfo(CoreIR::Instance *reg, CoreIR::Instance *mux, bool mux_in_port)
      : can_replace(true), reg(reg), mux(mux), mux_in_port(mux_in_port) {}
};

// Checks if inst of generated module and generated module has the following
// name
bool instance_of(CoreIR::Instance *inst, std::string ns, std::string name) {
  auto mod = inst->getModuleRef();
  if (!mod->isGenerated()) {
    return false;
  }
  auto gen = mod->getGenerator();
  return gen->getName() == name && gen->getNamespace()->getName() == ns;
}
CoreIR::Instance *get_instance(CoreIR::Wireable *w) {
  auto parent = w->getTopParent();
  if (auto inst = CoreIR::dyn_cast<CoreIR::Instance>(parent)) {
    return inst;
  }
  return nullptr;
}

CoreIR::Wireable *get_driver(CoreIR::Wireable *w) {
  auto conns = w->getConnectedWireables();
  ASSERT(conns.size() == 1, "NYI, non-bitvector connection");
  return *conns.begin();
}

CEInfo check_register(CoreIR::Instance *reg) {
  auto reg_driver = get_driver(reg->sel("in"));
  auto mux = get_instance(reg_driver);
  // Conditions that need to hold:
  // is an instance
  // is a generated module
  // generatorRef is coreir.mux
  // mux.out is reg_driver
  // mux.out has a single connection
  if (mux == nullptr || !instance_of(mux, "coreir", "mux") ||
      mux->sel("out") != reg_driver ||
      mux->sel("out")->getConnectedWireables().size() != 1) {
    return CEInfo();
  }
  // either mux.in0 or mux.in1 is driven by reg.out
  if (get_driver(mux->sel("in0")) == reg->sel("out")) {
    return CEInfo(reg, mux, 1);
  }
  else if (get_driver(mux->sel("in1")) == reg->sel("out")) {
    return CEInfo(reg, mux, 0);
  }
  return CEInfo();
}
} // namespace

namespace CoreIR {
namespace Passes {
bool ClockGate::runOnModule(Module *m) {
  // Find the clock gating pattern (a register driving a mux driving the
  // register)
  if (!m->hasDef()) {
    return false;
  }
  auto def = m->getDef();
  std::vector<CEInfo> to_replace;
  for (auto ipair : def->getInstances()) {
    auto inst = ipair.second;
    if (instance_of(inst, "coreir", "reg")) {
      auto info = check_register(inst);
      if (info.can_replace) {
        to_replace.push_back(info);
      }
    }
  }
  for (auto info : to_replace) {
    auto replace_name = info.reg->getInstname() + "__CE";
    auto width = info.reg->getModuleRef()->getGenArgs()["width"];
    auto ce_inst =
        def->addInstance(replace_name, "mantle.regCE", {{"width", width}});

    // Connect the clock
    auto clk_driver = get_driver(info.reg->sel("clk"));
    def->connect(clk_driver, ce_inst->sel("clk"));

    // Connect mux input
    auto regCE_driver =
        get_driver(info.mux->sel("in" + std::to_string(info.mux_in_port)));
    def->connect(regCE_driver, ce_inst->sel("in"));

    // Connect mux select
    auto regSel_driver = get_driver(info.mux->sel("sel"));
    if (info.mux_in_port == 0) {
      // not the select first
      auto not_inst_name = "not_inst" + this->getContext()->getUnique();
      auto not_inst = def->addInstance(not_inst_name, "corebit.not");
      def->connect(regSel_driver, not_inst->sel("in"));
      regSel_driver = not_inst->sel("out");
    }
    def->connect(regSel_driver, ce_inst->sel("ce"));

    // Connect the output(s) easiest is to leverage a passthrough
    auto pt = addPassthrough(info.reg->sel("out"), "_pt");

    // Remove the mux and register
    def->removeInstance(info.reg);
    def->removeInstance(info.mux);

    def->connect(ce_inst->sel("out"), pt->sel("in"));
    inlineInstance(pt);
  }

  return to_replace.size() > 0;
} // runOnModule
} // namespace Passes
} // namespace CoreIR
