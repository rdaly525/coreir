
#include "coreir.h"
#include "coreir/passes/transform/flattentypes.h"
#include <set>

using namespace std;
using namespace CoreIR;
namespace {
inline bool isBit(Type* t) {
  return t->isBaseType() || isa<NamedType>(t);
}
bool isBitOrArrOfBits(Type* t) {
  if (isBit(t)) return true;
  if (auto at = dyn_cast<ArrayType>(t)) {
    return isBit(at->getElemType());
  }
  return false;
}

//Gets all the ports that are not the top level
void getPortList(Type* t, SelectPath cur,vector<std::pair<SelectPath,Type*>>& ports,vector<string>& uports) {
  if (isBitOrArrOfBits(t)) {
    if (cur.size()>1) {
      ports.push_back({cur,t});
    }
    else {
      uports.push_back({cur[0]});
    }
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    for (uint i=0; i<at->getLen(); ++i) {
      SelectPath next = cur;
      next.push_back(to_string(i));
      getPortList(at->getElemType(),next,ports,uports);
    }
  }
  else if (auto rt = dyn_cast<RecordType>(t)) {
    for (auto record : rt->getRecord()) {
      SelectPath next = cur;
      next.push_back(record.first);
      getPortList(record.second,next,ports,uports);
    }
  }
  else {
    cout << t->toString() << endl;
    assert(0);
  }
}

}//namespace

std::string Passes::FlattenTypes::ID = "flattentypes";
bool Passes::FlattenTypes::runOnInstanceGraphNode(InstanceGraphNode& node) {
  //Outline of algorithm.
  //For every non-flattened field of Record type:
  //Create a new flattened field, add it to the module type (hopefully no collisions!)
  //Add a passthrough around interface and each instance of this module. reconnect passthrough to 
  //  new flattened ports.
  //delete the passthrough
  
  Module* mod = node.getModule();
  
  //If it is a generator or has no def:
  //Make sure all instances already have flat types
  if (!mod->hasDef()) {
    for (auto rpair : mod->getType()->getRecord()) {
      ASSERT(isBitOrArrOfBits(rpair.second),
      "NYI flatten types of generator or nodef module\n{"+mod->getRefName()+"}."+rpair.first + " Is not a flattened type!\n  Type is: " + rpair.second->toString()); 
    }
  }
 
  ModuleDef* def = mod->getDef();
  
  //Get a list of all the correct ports necessary. 
  vector<std::pair<SelectPath,Type*>> ports;
  vector<string> unchanged;
  getPortList(mod->getType(),{},ports,unchanged);

  //Early out if no new ports
  if (ports.size()==0) return false;

  //Create a list of new names for the ports
  vector<std::pair<string,Type*>> newports;
  unordered_set<string> verifyUnique;
  for (auto portpair : ports) {
    string newport = join(portpair.first.begin(),portpair.first.end(),string("_"));
    ASSERT(verifyUnique.count(newport)==0,"NYI: Name clashes");
    newports.push_back({newport,portpair.second});
    verifyUnique.insert(newport);
  }

  //Append new ports to this module (should not affect any connections)
  for (auto newportpair : newports) {
    node.appendField(newportpair.first,newportpair.second);
  }

  //TODO use definition of instance itsefl

  //Now the fun part.
  //Get a list of interface + instances
  vector<Wireable*> work;
  work.push_back(def->getInterface());
  for (auto inst : node.getInstanceList()) {
    work.push_back(inst);
  }
  
  for (auto w : work) {
    ModuleDef* wdef = w->getContainer();
    
    //Add passtrhough to isolate the ports
    auto pt = addPassthrough(w,"_pt" + this->getContext()->getUnique());
    
    //disconnect passthrough from wireable
    wdef->disconnect(pt->sel("in"),w);

    //connect all old ports of passtrhough to new ports of wireable
    for (uint i=0; i<ports.size(); ++i) {
      wdef->connect(pt->sel("in")->sel(ports[i].first), w->sel(newports[i].first));
    }
    //reconnect all unchanged ports
    for (auto p : unchanged) {
      wdef->connect(pt->sel("in")->sel(p),w->sel(p));
    }

    //inline the passthrough
    inlineInstance(pt);
  }

  //Now delete the old ports
  std::set<string> oldports;
  for (auto portpair : ports) {
    oldports.insert(portpair.first[0]);
  }
  for (auto port : oldports) {
    node.detachField(port);
  }
  //Conservatively assume you modifieid it
  return oldports.size()>0;

}
