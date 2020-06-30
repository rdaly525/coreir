#include "coreir/passes/analysis/instancecount.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

namespace {
void incrementMap(
  std::map<string, std::pair<int, int>>& map,
  string name,
  int val0,
  int val1) {
  if (map.count(name)) {
    map[name].first += val0;
    map[name].second += val1;
  }
  else {
    map[name].first = val0;
    map[name].second = val1;
  }
}
}  // namespace

bool Passes::InstanceCount::runOnInstanceGraphNode(InstanceGraphNode& node) {

  // Create a new Vmodule for this node
  Module* m = node.getModule();
  if (!m->hasDef()) {
    string mnsname = m->getNamespace()->getName();
    if (mnsname != "coreir" && mnsname != "corebit") {
      this->missingDefs.insert(m);
    }
    return false;
  }
  this->modOrder.push_back(m);

  std::map<string, std::pair<int, int>> primmap;
  for (auto instpair : m->getDef()->getInstances()) {
    Instance* inst = instpair.second;
    Module* imod = inst->getModuleRef();
    string nsname = inst->getModuleRef()->getNamespace()->getName();
    string longname = inst->getModuleRef()->getLongName();
    if (nsname == "coreir" || nsname == "corebit") {
      incrementMap(primmap, longname, 1, 0);
    }
    else if (this->cntMap.count(imod)) {
      for (auto cntpair : this->cntMap[imod]) {
        incrementMap(
          primmap,
          cntpair.first,
          0,
          cntpair.second.first + cntpair.second.second);
      }
    }
    else {
      ASSERT(this->missingDefs.count(imod) > 0, imod->getLongName());
    }
  }
  this->cntMap[m] = primmap;
  return false;
}

bool Passes::InstanceCount::finalize() {
  // For now just print to Stdout
  cout << "An instance count of all the primitives" << endl;
  cout << "=======================================" << endl;
  for (auto m : this->modOrder) {
    cout << m->getLongName();
    if (this->missingDefs.count(m)) { cout << "| Missing def " << endl; }
    else {
      ASSERT(this->cntMap.count(m), "Bug in Pass" + m->getLongName());
      cout << " | instances in current | instances in children | " << endl;
      for (auto cntpair : cntMap[m]) {
        cout << "  " << cntpair.first << " | " << cntpair.second.first << " | "
             << cntpair.second.second << endl;
      }
    }
    cout << endl;
  }
  cout << "=======================================" << endl;
  return false;
}
