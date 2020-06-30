#include "coreir/passes/analysis/verifyconnectivity.h"
#include "coreir.h"
#include "coreir/tools/cxxopts.h"

using namespace std;
using namespace CoreIR;

namespace {
bool IsVerilogDefn(ModuleDef* defn) {
  const auto& metadata = defn->getModule()->getMetaData();
  return metadata.count("verilog") > 0;
}
}  // namespace

void Passes::VerifyConnectivity::initialize(int argc, char** argv) {
  cxxopts::Options options(
    "verifyconnectivity",
    "verifys the connectivty of the hardware graph");
  options.add_options()("h,help", "help")("i,onlyinputs", "Only checks inputs")(
    "c,noclkrst",
    "Do not check clocks");
  auto opts = options.parse(argc, argv);
  if (opts.count("i")) { this->onlyInputs = true; }
  if (opts.count("c")) { this->checkClkRst = false; }
}

bool Passes::VerifyConnectivity::checkIfFullyConnected(Wireable* w, Error& e) {
  if (this->onlyInputs && w->getType()->isOutput()) { return true; }
  if (auto rt = dyn_cast<RecordType>(w->getType())) {
    if (rt->getRecord().size() == 0) return true;
  }

  Context* c = this->getContext();
  if (w->getConnectedWireables().size() > 0) return true;
  if (auto nt = dyn_cast<NamedType>(w->getType())) {
    bool crin = nt == c->Named("coreir.clkIn") ||
      nt == c->Named("coreir.arstIn");
    bool crout = nt == c->Named("coreir.clk") || nt == c->Named("coreir.arst");
    if (!this->checkClkRst && (crin || (!this->onlyInputs && crout))) {
      return true;
    }
    e.message(
      "{" + w->getContainer()->getName() + "}." + w->toString() +
      " Is not fully connected (N)");
    return false;
  }
  if (w->getSelects().size() == 0) {
    w->getContainer()->print();
    e.message(
      "{" + w->getContainer()->getName() + "}." + w->toString() +
      " Is not connected");
    if (w->getContainer()->getModule()->isGenerated()) {
      e.message(
        "with params=" +
        toString(w->getContainer()->getModule()->getGenArgs()));
    }
    e.fatal();
    w->getContext()->error(e);
    return false;
  }
  if (auto rt = dyn_cast<RecordType>(w->getType())) {
    bool isConnected = true;
    for (auto field : rt->getFields()) {
      isConnected &= checkIfFullyConnected(w->sel(field), e);
    }
    if (!isConnected) {
      e.message(
        "{" + w->getContainer()->getName() + "}." + w->toString() +
        " Is not fully connected (R)");
    }
    return isConnected;
  }
  else if (auto at = dyn_cast<ArrayType>(w->getType())) {
    bool isConnected = true;

    // Collect slice connections ranges, we will skip these since they are
    // already connected
    std::deque<std::pair<uint, uint>> ranges_to_skip;
    for (auto sel : w->getSelects()) {
      std::string selStr = sel.second->getSelStr();
      if (isSlice(selStr)) { ranges_to_skip.push_back(parseSlice(selStr)); }
    }

    // Sort in ascending order by slice beginning (first elem of pair)
    sort(ranges_to_skip.begin(), ranges_to_skip.end());

    for (uint i = 0; i < at->getLen(); ++i) {
      // If we're greater than or equal to the current slice to skip's end idx,
      // remove slice (iteratively since we may have overlapping slices)
      while (ranges_to_skip.size() && i >= ranges_to_skip[0].second) {
        ranges_to_skip.pop_front();
      }
      // If we're greater than the current slice to skip's start idx,
      // continue
      if (ranges_to_skip.size() && i >= ranges_to_skip[0].first) continue;

      // TODO bug with named types here
      if (!w->canSel(to_string(i))) {
        e.message(
          "{" + w->getContainer()->getName() + "}." + w->toString() + "." +
          to_string(i) + " Is not fully connected (A)");
        return false;
      }
      isConnected &= checkIfFullyConnected(w->sel(i), e);
    }
    return isConnected;
  }
  else {
    ASSERT(0, "CANNOT HANDLE TYPE: " + w->getType()->toString());
    return false;
  }
}

bool Passes::VerifyConnectivity::runOnModule(Module* m) {
  // Check if all ports are connected for everything.
  Context* c = this->getContext();
  ModuleDef* def = m->getDef();

  if (IsVerilogDefn(def)) { return false; }

  Error e;
  bool verify = true;
  verify &= checkIfFullyConnected(def->getInterface(), e);
  for (auto inst : def->getInstances()) {
    verify &= checkIfFullyConnected(inst.second, e);
  }
  if (!verify) {
    c->error(e);
    c->printerrors();
  }
  return false;
}
