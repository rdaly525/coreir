
/*
 * Make sure you start at hellomodule.h before this one.
 *
 * This is just filling out some function definitions
 */

#include "coreir.h"
#include "coreir/passes/transform/adddirected.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::AddDirected::ID = "adddirected";
bool Passes::AddDirected::runOnModule(Module* m) {
  
  if (!m->hasDef()) return false;
  DirectedModule dm(m); 
  json j(json::value_t::array);
  bool changed = false;
  for (auto dc : dm.getConnections()) {
    changed = true;
    auto srcpath = dc->getSrc();
    auto snkpath = dc->getSnk();
    string srcstr = join(srcpath.begin(),srcpath.end(),string("."));
    string snkstr = join(snkpath.begin(),snkpath.end(),string("."));
    j.push_back(srcstr);
    j.push_back(snkstr);
  }
  if (changed) {
    m->getMetaData()["directedconnections"] = j;
  }
  return changed;
}
