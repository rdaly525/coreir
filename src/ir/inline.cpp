#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/passmanager.h"
#include "coreir/ir/instance_graph_logger.hpp"

using namespace std;

namespace CoreIR {

// This helper will connect everything from wa to wb with a spDelta.
// spDelta is the SelectPath delta to get from wa to wb
void connectOffsetLevel(
  ModuleDef* def,
  Wireable* wa,
  SelectPath spDelta,
  Wireable* wb) {

  for (auto waCon : wa->getConnectedWireables()) {
    for (auto wbCon : wb->getConnectedWireables()) {  // was inw
      SelectPath wbConSPath = wbCon->getSelectPath();
      SelectPath waConSPath = waCon->getSelectPath();

      // concatenate the spDelta into wa
      waConSPath.insert(waConSPath.end(), spDelta.begin(), spDelta.end());
      def->connect(waConSPath, wbConSPath);
    }
  }

  // Traverse down the wb keeping wa constant
  for (auto wbselmap : wb->getSelects()) {
    SelectPath td = spDelta;
    td.push_back(wbselmap.first);
    connectOffsetLevel(def, wa, td, wbselmap.second);
  }
}

// This helper will connect a single select layer of the passthrough.
void connectSameLevel(ModuleDef* def, Wireable* wa, Wireable* wb) {

  // cout << "Connecting same level" << endl;

  // wa should be the flip type of wb
  assert(wa->getType() == wb->getType()->getFlipped());

  auto waSelects = wa->getSelects();
  auto wbSelects = wb->getSelects();

  set<string> both;
  for (auto waSelmap : waSelects) {
    if (wbSelects.count(waSelmap.first) > 0) { both.insert(waSelmap.first); }
  }

  // Traverse another same level for both
  for (auto selstr : both) {
    connectSameLevel(def, waSelects[selstr], wbSelects[selstr]);
  }

  // Connect wb to all the subselects of wa
  for (auto spair : waSelects) {
    connectOffsetLevel(def, wb, {spair.first}, spair.second);
  }

  // Connect wa to all the subselects of wb
  for (auto spair : wbSelects) {
    connectOffsetLevel(def, wa, {spair.first}, spair.second);
  }

  // cout << "Connecting possible N^2 wireables" << endl;

  // Now connect all N^2 possible connections for this level
  for (auto waCon : wa->getConnectedWireables()) {
    for (auto wbCon : wb->getConnectedWireables()) {
      def->connect(waCon, wbCon);
    }
  }

  // cout << "Done connecting wireables" << endl;
}

// Generate a unique mantle wire instance for slice passthrough logic,
// we use the instance input port name (select path to string) but for safety
// we check existing instance names and make sure it's unique
std::string makeUniqueInstanceName(ModuleDef* def, Wireable* from) {
  SelectPath select_path = from->getSelectPath();
  std::string inst_name = join(
    select_path.begin(),
    select_path.end(),
    std::string("_"));
  auto instances = def->getInstances();
  if (!instances.count(inst_name)) { return inst_name; }
  int count = 0;
  while (instances.count(inst_name + std::to_string(count))) { count++; }
  return inst_name + std::to_string(count);
}

namespace {
void PTTraverse(ModuleDef* def, Wireable* from, Wireable* to) {
  for (auto other : from->getConnectedWireables()) { def->connect(to, other); }
  vector<Wireable*> toDelete;
  for (auto other : from->getConnectedWireables()) {
    toDelete.push_back(other);
  }
  for (auto other : toDelete) { def->disconnect(from, other); }

  // If we encounter a slice, we insert a wire so the passthrough logic works
  // (it was originally written before slices were implemented, so assumes there
  // are no slices)
  for (auto sel : from->getSelects()) {
    if (isSlice(sel.first)) {
      // Only inline instance input wires if there's a single driver,
      // otherwise, it will generate a concat node that shouldn't be inlined
      // since we avoid inserting expressions into instance inputs
      Context* c = def->getContext();
      Instance* wire = def->addInstance(
        makeUniqueInstanceName(def, from),
        c->getGenerator("mantle.wire"),
        {{"type", Const::make(c, from->getType())}});
      wire->getMetaData()["inline_verilog_wire"] = true;
      def->connect(to, wire->sel("in"));
      wire->getModuleRef()->runGenerator();
      to = wire->sel("out");
      break;
    }
  }
  for (auto sels : from->getSelects()) {
    if (!isa<InstanceSelect>(sels.second)) {
      PTTraverse(def, sels.second, to->sel(sels.first));
    }
  }
}
}  // namespace

// addPassthrough will create a passthrough Module for Wireable w with name
// <name> This buffer has interface {"in": Flip(w.Type), "out": w.Type}
// There will be one connection connecting w to name.in, and all the connections
// that originally connected to w connecting to name.out which has the same type
// as w
Instance* addPassthrough(Wireable* w, string instname) {

  // First verify if I can actually place a passthrough here
  // This means that there can be nothing higher in the select path tha is
  // connected
  Context* c = w->getContext();
  Wireable* wcheck = w;
  while (Select* wchecksel = dyn_cast<Select>(wcheck)) {
    wcheck = wchecksel->getParent();
    ASSERT(
      wcheck->getConnectedWireables().size() == 0,
      "Cannot add a passthrough to a wireable with connected selparents");
  }
  ModuleDef* def = w->getContainer();
  Type* wtype = w->getType();

  // Add actual passthrough instance
  Instance* pt = def->addInstance(
    instname,
    c->getGenerator("_.passthrough"),
    {{"type", Const::make(c, wtype)}});

  set<Wireable*> completed;
  PTTraverse(def, w, pt->sel("out"));

  // Connect the passthrough back to w
  def->connect(w, pt->sel("in"));

  return pt;
}

// This will inline an instance of a passthrough
void inlinePassthrough(Instance* i) {

  ModuleDef* def = i->getContainer();

  // This will recursively connect all the wires together
  connectSameLevel(def, i->sel("in"), i->sel("out"));

  // Now delete this instance
  def->removeInstance(i);
}

// This will modify the moduledef to inline the instance
bool inlineInstance(Instance* inst) {
  auto c = inst->getContext();


  // Special case for a passthrough
  // TODO should have a better check for passthrough than string compare
  Module* mref = inst->getModuleRef();
  if (
    mref->isGenerated() &&
    mref->getGenerator()->getRefName() == "_.passthrough") {
    // cout << "Inlining: " << toString(inst) << endl;
    inlinePassthrough(inst);
    return true;
  }

  //Bit of a hack
  assert(c->isDebug());
  bool old_debug = c->isDebug();
  c->getPassManager()->setDebug(false);



  Values instModArgs = inst->getModArgs();
  ModuleDef* def = inst->getContainer();
  Module* modInline = mref;

  if (!modInline->hasDef()) {
    return false;
  }
  string instname = inst->getInstname();

  // I will be inlining defInline into def
  // Making a copy because i want to modify it first without modifying all of
  // the other instnaces of modInline
  ModuleDef* defInline = modInline->getDef()->copy();

  // Add a passthrough Module to quarentine 'self'
  addPassthrough(defInline->getInterface(), "_insidePT");

  string inlinePrefix = inst->getInstname() + "$";


  //Store debug table information
  std::vector<std::tuple<std::string, std::string, std::string>> debug_info;
  // First add all the instances of defInline into def with a new name
  for (auto &[sub_iname, sub_inst] : defInline->getInstances()) {
    string iname = inlinePrefix + sub_iname;
    Values modargs = sub_inst->getModArgs();
    // Should do this in a more generic way
    for (auto vpair : modargs) {
      if (Arg* varg = dyn_cast<Arg>(vpair.second)) {
        ASSERT(instModArgs.count(varg->getField()), "DEBUG ME");
        modargs[vpair.first] = instModArgs[varg->getField()];
      }
    }
    Instance* new_inst = def->addInstance(
      iname,
      sub_inst->getModuleRef(),
      modargs);
    new_inst->setMetaData(sub_inst->getMetaData());
    if (old_debug) {
      auto sub_mname = sub_inst->getModuleRef()->getRefName();
      if (sub_mname != "_.passthrough") {
        debug_info.push_back(
          {sub_iname, iname, sub_inst->getModuleRef()->getRefName()});
      }
    }
  }

  // Now add all the easy connections (that do not touch the boundary)
  for (auto cons : defInline->getConnections()) {
    SelectPath pA = cons.first->getSelectPath();
    SelectPath pB = cons.second->getSelectPath();

    // Easy case: when neither are connect to self
    if (pA[0] != "self" && pB[0] != "self") {
      // Create the correct names and connect
      pA[0] = inlinePrefix + pA[0];
      pB[0] = inlinePrefix + pB[0];
      def->connect(pA, pB);
    }
  }

  // Create t3e Passthrough to quarentene the instance itself
  Instance* outsidePT = addPassthrough(inst, "_outsidePT");

  // Connect the two passthrough buffers together ('in' ports are facing the
  // boundary)
  def->connect("_outsidePT.in", inlinePrefix + "_insidePT.in");

  // Now remove the instance (which will remove all the previous connections)
  std::string orig_iname = inst->getInstname();
  def->removeInstance(inst);

  // Now inline both of the passthroughs
  inlineInstance(outsidePT);

  inlineInstance(cast<Instance>(def->sel(inlinePrefix + "_insidePT")));

  c->getPassManager()->setDebug(old_debug);
  if (c->isDebug()) {
    std::string parent = def->getModule()->getRefName();
    //Log removing old instance
    auto igl = c->getPassManager()->getInstanceGraphLogger();
    igl->logRemoveInstance(def->getModule()->getRefName(), orig_iname);
    for (auto &[sub_iname, inew, sub_mname] : debug_info) {
      //Log adding new instance
      igl->logNewInstance(parent, sub_mname, inew);
      igl->logInlineInstance(parent, orig_iname, sub_iname, inew);
    }
  }


  return true;
}

}  // namespace CoreIR
