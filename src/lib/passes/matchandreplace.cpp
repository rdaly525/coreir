#include "coreir.h"
#include "coreir-pass/passes.h"
#include "matchandreplace.hpp"

#include <algorithm>

using namespace CoreIR;

using namespace std;

void MatchAndReplacePass::verifyOpts(Opts opts) {
  
  //Verify that pattern and replace have the same exact type.
  ASSERT(pattern->getType() == replacement->getType(),"Pattern and Replace need the same type");
  ASSERT(pattern->hasDef(),"pattern needs to have a definition!");

  ASSERT( ((opts.configargs.size() > 0) && (!!opts.getConfigArgs)) == false,"Cannot provide configargs and getConfigArgs at the same time")
  if (opts.instanceKey.size() > 0) {
    auto key = opts.instanceKey;
    //Verify that each instance is a unique instance of pattern.
    ASSERT(key.size()==pattern->getDef()->getInstances().size(),"InstanceKey must contain each instance from pattern")
    for (auto instmap : pattern->getDef()->getInstances()) {
      if (find(key.begin(),key.end(),instmap.first) == key.end()) {
        ASSERT(false, "InstanceKey must contain each instance from pattern");
      }
    }
  }

}

//This should load instanceKey, inCons, exCons
void MatchAndReplacePass::preprocessPattern() {
  cout << "NEW PATTERN" << endl;
  ModuleDef* pdef = pattern->getDef();
  //Just load it in whatever order if it is 0
  if (instanceKey.size()==0) {
    for (auto instmap : pdef->getInstances()) {
      instanceKey.push_back(instmap.first);
    }
  }

  //create a backwards map from str -> uint for key
  unordered_map<string,uint> reverseKey;
  for (uint i=0; i<instanceKey.size(); ++i) {
    reverseKey[instanceKey[i]] = i;
  }

  //Initialize Internal/ExternalConnections
  for (uint i=0; i<instanceKey.size(); ++i) {
    this->inCons.push_back(unordered_map<SelectPath,vector<std::pair<SelectPath,uint>>>());
    this->exCons.push_back(vector<std::pair<SelectPath,SelectPath>>());
  }

  //Temporary cache so no double internal edges.
  //{keyIdx,{path_for_keyidx,connectedpath}}
  unordered_set<myPair<uint,myPair<SelectPath,SelectPath>>> inConCache;

  //Load InternalConnections structure and ExternalConnections structure
  for (uint i=0; i<instanceKey.size(); ++i) {
    unordered_map<SelectPath,vector<pair<SelectPath,uint>>> exConsi;
    LocalConnections lcons = pdef->sel(instanceKey[i])->getLocalConnections();
    for (auto vcon : lcons) {
      SelectPath pathLocal = vcon.first->getSelectPath();
      pathLocal.pop_front();
      SelectPath pathConnected = vcon.second->getSelectPath();
      string conInst = pathConnected[0];
      pathConnected.pop_front();
      if (conInst=="self") { //This is an external connection
        this->exCons[i].push_back({pathLocal,pathConnected});
      }
      else { //This is an internal connection
        assert(reverseKey.count(conInst)==1);
        uint conIdx = reverseKey[conInst];
        if (inConCache.count({conIdx,{pathConnected,pathLocal}}) > 0) {
          continue;
        }
        this->inCons[i][pathLocal].push_back({pathConnected,conIdx});
        inConCache.insert({i,{pathLocal,pathConnected}});
      }
    }
  }

}


bool MatchAndReplacePass::runOnModule(Module* m) {
  
  Context* c = container->getContext();
  Module* container = m;
  //Checking for valid inputs
  
  //pattern module interface must be the same as the replacement interface
  ASSERT(pattern->getType() == replacement->getType(),"Pattern type != replacement type!\n" + pattern->getType()->toString() + "\n" + replacement->getType()->toString());
  
  //configargs shoud be the same as replacement params
  //checkArgsAreParams(configargs, replacement->getConfigParams());
 
  ModuleDef* pdef = pattern->getDef();
  ModuleDef* cdef = container->getDef();
  ModuleDef::InstanceMapType cinstMap = cdef->getInstanceMap();

  //If this module contains none of the any of the pattern modules, I will never find a match, so just return
  for (auto pi : pdef->getInstanceMap()) {
    if (!cinstMap.count(pi.first)) return false;
  }
  
  //Keep track of matched instances. This should correspond to instanceKey
  vector<Instance*> matched;

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
    //TODO this is origianl. Instance* rinst = cdef->addInstance(cinst->getInstname()+c->getUnique(),replacement,this->getConfigArgs(cinst));
    Instance* rinst = cdef->addInstance(cinst->getInstname()+c->getUnique(),replacement);
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
