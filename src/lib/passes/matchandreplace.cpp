#include "coreir.h"
#include "coreir-pass/passes.h"
#include "matchandreplace.hpp"

#include <algorithm>

using namespace CoreIR;

using namespace std;

void MatchAndReplacePass::verifyOpts(Opts opts) {
  ASSERT( (opts.configargs.size() > 0) && (opts.getConfigArgs) == false,"Cannot provide configargs and getConfigArgs at the same time")
  if (opts.instanceKey.size() > 0) {
    auto key = opts.instanceKey;
    //Verify that each instance is a unique instance of pattern.
    ASSERT(key.size()==patern->getInstances().size(),"InstanceKey must contain each instance from pattern")
    for (auto instmap : pattern->getInstances()) {
      if (find(key.begin(),key.end(),instmap.first) == key.end()) {
        ASSERT(false, "InstanceKey must contain each instance from pattern");
      }
    }
  }

  //TODO potentally more checks
}

//This should load instanceKey, inCons, exCons
bool MatchAndReplacePass::preprocessPattern() {
  
  //Just load it in whatever order if it is 0
  if (instanceKey.size()==0) {
    for (auto instmap : pattern->getInstances()) {
      instanceKey.push_back(instmap.first);
    }
  }

  //create a backwards map from str -> uint for key
  unordered_map<string,uint> reverseKey;
  for (uint=0; i<instanceKey.size(); ++i) {
    reverseKey[instanceKey[i]] = i;
  }

  //Load InternalConnections structure
  for (uint i=0; i<instanceKey.size(); ++i) {
    unordered_map<SelectPath,vector<pair<SelectPath,uint>>> exConsi;
    LocalConnections lcons = pattern->sel(instanceKey[i]])->getLocalConnections();
    for (auto vcon : lcons) {
      SelectPath pathLocal = vcon.first->getSelectPath();
      SelectPath pathConnected = vcon.second->getSelectPath();
    }
  }


}


bool MatchAndReplacePass::runOnModule(Module* m) {
  
  Module* container = m;
  //Checking for valid inputs
  
  //pattern module interface must be the same as the replacement interface
  ASSERT(pattern->getType() == replacement->getType(),"Pattern type != replacement type!\n" + pattern->getType()->toString() + "\n" + replacement->getType()->toString());
  
  //configargs shoud be the same as replacement params
  //checkArgsAreParams(configargs, replacement->getConfigParams());
 
  ModuleDef* pdef = pattern->getDef();
  ModuleDef* cdef = container->getDef();
  ModuleDef::InstanceMapType cinstMap = cdef->getInstanceMap();

  //If this module contains none of the pattern modules, I will never find a match, so just return
  for (auto pi : pdef->getInstanceMap()) {
    if (!cinstMap.count(pi.first)) return false;
  }

  //Start with only the pattern being a single thing
  ASSERT(pdef->getInstances().size()==1,"NYI patterns with multiple instances");
  
  Context* c = container->getContext();

  //The only instance
  Instantiable* pi = pdef->getInstanceMap().begin()->first;
  Instance* pinst = *pdef->getInstanceMap()[pi].begin();
  
  //Can only deal with generators
  ASSERT(pinst->isGen(),"NYI Cannot do patterns of non generators");
  Args pgenargs = pinst->getGenargs();
  
  //Keep list of matching instances to delete afterwards
  std::vector<Instance*> matches;
  std::vector<string> passthroughToInline;

  for (auto cinst : cinstMap[pi]) {
    //Check if the genargs are the same
    if (!(cinst->getGenargs() == pgenargs)) {
      continue;
    }
    
    //TODO Assuming that the connections are correct
    matches.push_back(cinst);
    Instance* rinst = cdef->addInstance(cinst->getInstname()+c->getUnique(),replacement,this->getConfigArgs(cinst));
    string cbufName = "_cbuf"+c->getUnique();
    passthroughToInline.push_back(cbufName);
    addPassthrough(cinst,cbufName);
    //TODO These connections could be preprocessed
    for (auto con : pdef->getConnections()) {
      
      //Get and sort the paths
      SelectPath apath = con.first->getSelectPath();
      SelectPath bpath = con.second->getSelectPath();
      SelectPath rpath, cpath;
      assert(apath[0] == "self" || bpath[0] == "self");
      if (apath[0] == "self") {
        rpath = apath;
        cpath = bpath;
      }
      else if(bpath[0] == "self") {
        rpath = bpath;
        cpath = apath;
      }
      else {
        assert(0);
      }
      //update the paths to be consistent 
      rpath[0] = rinst->getInstname();
      cpath[0] = "in";
      cpath.push_front(cbufName);
      cdef->connect(rpath,cpath);
    }
  }

  bool found = matches.size() > 0;
  //Now delete all the matched instances
  for (auto inst : matches) {
    cdef->removeInstance(inst);
  }
 
  //Now inline all the passthrough Modules
  for (auto selstr : passthroughToInline) {
    inlineInstance(cast<Instance>(cdef->sel(selstr)));
  }
  
  cdef->validate();
  return found;
}
