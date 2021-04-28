
#include "coreir/passes/transform/flattentypes.h"
#include <set>
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/tools/cxxopts.h"
#include "coreir/ir/symbol_table_interface.hpp"

using namespace std;
using namespace CoreIR;

bool CoreIR::Passes::FlattenTypes::isLeafType(Type* t) {
  if (this->preserve_ndarrays) { return isBitOrNDArrOfBits(t); }
  return isBitOrArrOfBits(t);
}

// Gets all the ports that are not the top level
void Passes::FlattenTypes::getPortList(
  Type* t,
  SelectPath cur,
  vector<std::pair<SelectPath, Type*>>& ports,
  vector<string>& uports) {
  if (this->isLeafType(t)) {
    if (cur.size() > 1) { ports.push_back({cur, t}); }
    else {
      uports.push_back({cur[0]});
    }
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    for (uint i = 0; i < at->getLen(); ++i) {
      SelectPath next = cur;
      next.push_back(to_string(i));
      this->getPortList(at->getElemType(), next, ports, uports);
    }
  }
  else if (auto rt = dyn_cast<RecordType>(t)) {
    for (auto record : rt->getRecord()) {
      SelectPath next = cur;
      next.push_back(record.first);
      this->getPortList(record.second, next, ports, uports);
    }
  }
  else {
    cout << t->toString() << endl;
    assert(0);
  }
}

bool Passes::FlattenTypes::runOnInstanceGraphNode(InstanceGraphNode& node) {
  // Outline of algorithm.
  // For every non-flattened field of Record type:
  // Create a new flattened field, add it to the module type (hopefully no
  // collisions!) Add a passthrough around interface and each instance of this
  // module. reconnect passthrough to
  //  new flattened ports.
  // delete the passthrough

  Module* mod = node.getModule();

  // If it is a generator or has no def:
  // Make sure all instances already have flat types

  // Get a list of all the correct ports necessary.
  vector<std::pair<SelectPath, Type*>> ports;
  vector<string> unchanged;
  this->getPortList(mod->getType(), {}, ports, unchanged);

  // Early out if no new ports
  if (ports.size() == 0) return false;

  // Create a list of new names for the ports
  vector<std::pair<string, Type*>> newports;
  unordered_set<string> verifyUnique;
  for (auto &[sp, type] : ports) {
    string newport = join(
      sp.begin(),
      sp.end(),
      string("_"));
    ASSERT(verifyUnique.count(newport) == 0, "NYI: Name clashes");
    newports.push_back({newport, type});
    verifyUnique.insert(newport);
    if (getContext()->getDebug()) {
      this->getSymbolTable()->setPortName(
          mod->getLongName(), ::toString(sp), newport);
    }
  }

  // Append new ports to this module (should not affect any connections)
  for (auto newportpair : newports) {
    node.appendField(newportpair.first, newportpair.second);
  }

  // TODO use definition of instance itself

  // Now the fun part.
  // Get a list of interface + instances
  vector<Wireable*> work;

  if (mod->hasDef()) {
    ModuleDef* def = mod->getDef();
    work.push_back(def->getInterface());
  }
  else {
    for (auto rpair : mod->getType()->getRecord()) {
      if (!isBitOrArrOfBits(rpair.second)) {
        LOG(WARN)
          << "WARNING: Flattening type of generator or module with no "
             "definition, assumes definition follows the flatten types scheme, "
             "see https://github.com/rdaly525/coreir/issues/800 for more "
             "info\n{" +
            mod->getRefName() + "}." + rpair.first +
            " Is not a flattened type!\n  Type is: " + rpair.second->toString();
        break;  // only issue warning once
      }
    }
  }

  for (auto inst : node.getInstanceList()) { work.push_back(inst); }

  for (auto w : work) {
    ModuleDef* wdef = w->getContainer();

    // Add passtrhough to isolate the ports
    auto pt = addPassthrough(w, "_pt" + this->getContext()->getUnique());

    // disconnect passthrough from wireable
    wdef->disconnect(pt->sel("in"), w);

    // connect all old ports of passtrhough to new ports of wireable
    for (uint i = 0; i < ports.size(); ++i) {
      wdef->connect(
        pt->sel("in")->sel(ports[i].first),
        w->sel(newports[i].first));
    }
    // reconnect all unchanged ports
    for (auto p : unchanged) {
      wdef->connect(pt->sel("in")->sel(p), w->sel(p));
    }

    // inline the passthrough
    inlineInstance(pt);
  }

  // Now delete the old ports
  std::set<string> oldports;
  for (auto portpair : ports) { oldports.insert(portpair.first[0]); }
  for (auto port : oldports) { node.detachField(port); }
  // Conservatively assume you modifieid it
  return oldports.size() > 0;
}

void Passes::FlattenTypes::initialize(int argc, char** argv) {
  cxxopts::Options options(
    "flattentypes",
    "Flattens record and array types into Bit or Array of Bit (optionally "
    "preserve multi-dimensional array of bits)");
  options.add_options()(
    "n,ndarray",
    "Preserve multi-dimensional array of bits (ndarrays)");
  auto opts = options.parse(argc, argv);
  if (opts.count("n")) { this->preserve_ndarrays = true; }
}
