#include "coreir/passes/transform/clock_gate.h"

namespace {
struct CEInfo {
  bool can_replace = false;
  CoreIR::Instance* reg = nullptr;
  CoreIR::Instance* mux = nullptr;
  int mux_in_port = 0;
  bool has_arst = false;
  CEInfo() : can_replace(false) {}
  CEInfo(CoreIR::Instance* reg, CoreIR::Instance* mux, int mux_in_port)
      : can_replace(true),
        reg(reg),
        mux(mux),
        mux_in_port(mux_in_port) {}
};

// Checks if inst of generated module and generated module has the following
// name
bool instance_of(CoreIR::Instance* inst, std::string ns, std::string name) {
  auto mod = inst->getModuleRef();
  if (!mod->isGenerated()) { return false; }
  auto gen = mod->getGenerator();
  return gen->getName() == name && gen->getNamespace()->getName() == ns;
}

CoreIR::Instance* get_instance(CoreIR::Wireable* w) {
  auto parent = w->getTopParent();
  if (auto inst = CoreIR::dyn_cast<CoreIR::Instance>(parent)) { return inst; }
  return nullptr;
}

CoreIR::Wireable* get_driver(CoreIR::Wireable* w) {
  auto conns = w->getConnectedWireables();
  if (conns.size() != 1) { return nullptr; }
  return *conns.begin();
}

CEInfo check_register(CoreIR::Instance* reg) {
  auto reg_driver = get_driver(reg->sel("in"));
  if (reg_driver == nullptr) { return CEInfo(); }
  auto mux = get_instance(reg_driver);
  // Conditions that need to hold:
  // is an instance
  // is a generated module
  // generatorRef is coreir.mux
  // mux.out is reg_driver
  // mux.out has a single connection
  bool mux_valid = mux != nullptr && instance_of(mux, "coreir", "mux") &&
    mux->sel("out") == reg_driver &&
    mux->sel("out")->getConnectedWireables().size() == 1;

  if (!mux_valid) { return CEInfo(); }
  // either mux.in0 or mux.in1 is driven by reg.out
  if (get_driver(mux->sel("in0")) == reg->sel("out")) {
    return CEInfo(reg, mux, 1);
  }
  else if (get_driver(mux->sel("in1")) == reg->sel("out")) {
    return CEInfo(reg, mux, 0);
  }
  return CEInfo();
}
}  // namespace

namespace CoreIR {
namespace Passes {
bool ClockGate::runOnModule(Module* m) {
  // Find the clock gating pattern (a register driving a mux driving the
  // register)
  if (!m->hasDef()) { return false; }
  auto def = m->getDef();
  std::vector<CEInfo> to_replace;
  for (auto ipair : def->getInstances()) {
    auto inst = ipair.second;
    bool is_coreir_reg = instance_of(inst, "coreir", "reg");
    bool is_coreir_reg_arst = instance_of(inst, "coreir", "reg_arst");
    if (is_coreir_reg || is_coreir_reg_arst) {
      // NYI clock being negedge
      if (!inst->getModArgs().at("clk_posedge")->get<bool>()) { continue; }
      // NYI arst being negedge
      if (
        is_coreir_reg_arst &&
        !inst->getModArgs().at("arst_posedge")->get<bool>()) {
        continue;
      }
      auto info = check_register(inst);
      if (info.can_replace) {
        info.has_arst = is_coreir_reg_arst;
        to_replace.push_back(info);
      }
    }
  }
  for (auto info : to_replace) {
    auto replace_name = info.reg->getInstname() + "__CE";
    auto width = info.reg->getModuleRef()->getGenArgs()["width"];
    std::string mod_name = std::string("mantle.regCE") +
      (info.has_arst ? "_arst" : "");
    auto ce_inst = def->addInstance(replace_name, mod_name, {{"width", width}});

    // Connect the clock
    auto clk_driver = get_driver(info.reg->sel("clk"));
    def->connect(clk_driver, ce_inst->sel("clk"));

    // Connect the reset
    if (info.has_arst) {
      auto rst_driver = get_driver(info.reg->sel("arst"));
      def->connect(rst_driver, ce_inst->sel("arst"));
    }

    // Connect mux input
    auto regCE_driver = get_driver(
      info.mux->sel("in" + std::to_string(info.mux_in_port)));
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
}  // runOnModule
}  // namespace Passes
}  // namespace CoreIR
