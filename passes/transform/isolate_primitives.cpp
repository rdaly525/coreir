#include "passes/transform/isolate_primitives.h"

std::string CoreIR::Passes::IsolatePrimitives::ID = "isolate_primitives";

// Creates a separate module that isolates all the primitive (coreir/corebit)
// instances

namespace CoreIR {
namespace Passes {
bool IsolatePrimitives::runOnModule(Module* m) {
  if (!m->hasDef()) return false;
  auto def = m->getDef();
  auto c = this->getContext();

  // get a map of only primitive instances
  auto primitiveInstances = filterOver(def->getInstances(), [](auto it) {
    auto nsname = it.second->getModuleRef()->getNamespace()->getName();
    return nsname == "coreir" || nsname == "corebit";
  });

  // early out
  if (primitiveInstances.size() == 0) return false;

  std::vector<std::pair<Wireable*, Wireable*>>
    internal_connections;  // prim <=> prim
  std::vector<std::pair<Wireable*, Wireable*>>
    external_connections;  // prim <=> other
  for (auto const& [wA, wB] : def->getConnections()) {
    // Put into two piles external and internal
    bool AIsPrimitive = primitiveInstances.count(wA->getSelectPath()[0]);
    bool BIsPrimitive = primitiveInstances.count(wB->getSelectPath()[0]);
    if (AIsPrimitive && BIsPrimitive) {
      internal_connections.push_back(std::make_pair(wA, wB));
    }
    else if (AIsPrimitive) {
      external_connections.push_back(std::make_pair(wA, wB));
    }
    else if (BIsPrimitive) {
      external_connections.push_back(std::make_pair(wB, wA));
    }
  }

  // Construct module type interface
  // maintain info for external, internal, and port name
  // disconnect external_connections
  RecordParams ports;
  std::vector<std::tuple<Wireable*, Wireable*, std::string>> boundary_info;
  for (auto const& [wP, wE] : external_connections) {
    std::string portName = c->getUnique();
    ports.push_back(std::make_pair(portName, wP->getType()));
    boundary_info.push_back(std::make_tuple(wP, wE, portName));
    def->disconnect(wP, wE);
  }

  // Create new prim module and definition
  auto primModule = c->getNamespace("_")->newModuleDecl(
    m->getName() + "_primitives",
    c->Record(ports));
  // Add all primitive instances into new module
  auto pdef = primModule->newModuleDef();
  for (auto const& [iname, inst] : primitiveInstances) {
    pdef->addInstance(iname, inst->getModuleRef(), inst->getModArgs());
  }

  // Internal connections
  for (auto const& [wA, wB] : internal_connections) {
    pdef->connect(wA->getSelectPath(), wB->getSelectPath());
  }

  // External connections
  for (auto const& [wP, _, portName] : boundary_info) {
    UNUSED(_);
    auto portSP = SelectPath({"self", portName});
    pdef->connect(wP->getSelectPath(), portSP);
  }
  primModule->setDef(pdef);

  // Create instance of prim module and connect appropriately
  auto primInst = def->addInstance("primitive_" + c->getUnique(), primModule);
  for (auto const& [_, connE, portName] : boundary_info) {
    UNUSED(_);
    def->connect(connE, primInst->sel(portName));
  }

  // remove all primtiive instnaces
  for (auto const& [_, inst] : primitiveInstances) {
    UNUSED(_);
    def->removeInstance(inst);
  }

  return true;

}  // runOnModule
}  // namespace Passes
}  // namespace CoreIR
