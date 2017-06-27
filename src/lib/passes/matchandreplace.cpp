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

Wireable* selWithCheck(Wireable* w, SelectPath path, bool* error) {
  if (path.size()==0) {
    return w;
  }
  string sel = path[0];
  if (!w->hasSel(sel)) {
    *error = true;
    return nullptr;
  }
  path.pop_front();
  return selWithCheck(w->sel(sel),path,error);
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
  
  //Cache of used instances (for matches)
  unordered_set<Instance*> usedInstances;

  //Keep track of matched instances. This should correspond to instanceKey
  vector<Instance*> matchedInstances(instanceKey.size());

  ////set of all matches to delete. 
  //vector<Instance*> matchesToDelete;
  
  //Keep list of passthrough instances to inline
  vector<Instance*> passthroughsToInline;
  
  //Final return value
  bool found = false;

  //always start with key0 
  Instance* pfirst = cast<Instance>(pdef->sel(instanceKey[0]));
  Instantiable* pfirstKind = pfirst->getInstantiableRef();

  for (auto cinst : cinstMap[pfirstKind]) {
    
    //Work queue. {idx,potential matching instance}
    std::queue<std::pair<uint,Instance*>> work;
    
    //Keep track of the number of successful instances
    uint numCompleted;
    
    //Keep track of instances completed or on queue
    unordered_set<uint> accountedFor;

    work.push({0,cinst});
    while (!work.empty()) {
      uint idx = work.front().first;
      Instance* minst = work.front().second;
      Instance* pinst = cast<Instance>(pdef->sel(instanceKey[idx]));
      
      //If mnist is already used, break.
      if (usedInstances.count(mnist)>0) {
        break;
      }

      //Check if the types are the same
      if (minst->getType() != pinst->getType() ) {
        break;
      }

      //Check if all internal paths are correct.
      bool pathsCorrect = true;
      for (auto lcons : this->inCons[idx]) {
        SelectPath localPath = lcons.first;
        SelectPath otherPath = lcons.second[0].first;
        uint otherIdx = lcons.second[0].second;

        //Get local Wireable, and check if it exists
        bool error = false;
        Wireable* localW = selWithCheck(minst,localPath,&error);
        if (error) {
          pathsCorrect = false;
          break;
        }
        
        //Check if the fanout is exactly the same
        ASSERT(lcons.second.size()==1,"NYI fanout"); //TODO handle fanout
        if (localW->getConnectedWireables().size() != lcons.second.size() ) {
          pathsCorrect = false;
          break;
        }
        
        Wireable* otherW = local->getConnectedWireables()[0];
        Wireable* otherTopW = otherW->getTopParent();
        
        Instance* otherInst;
        if (!(otherInst = dyn_cast<Instance>(otherTopW))) {
          pathsCorrect = false;
          break;
        }

        //check if otherInst is the correct Module Type
        if (pdef->sel(instanceKey[otherIdx])->getInstantiableRef() != otherInst->getInstantiableRef()) {
          pathsCorrect = false;
          break;
        }
        
        //Check to see if the other path exists
        Wireable* otherWCheck = selWithCheck(otherInst,otherPath,&error);
        if (error) {
          pathsCorrect = false;
          break;
        }

        //Check if it is the same as the connected path
        if (otherW != otherWCheck) {
          pathsCorrect = false;
          break;
        }


        //Add other instance to queue if not there
        if (accountedFor.count(otherIdx)==0) {
          work.push({otherIdx,otherInst});
        }
      }// End connections check

      //Found correct connection  
      if (pathsCorrect) {
        matchedInstances[idx] = mnist;
        numCompleted++;
      }
      
    }// End work queue

    //Checking if it completely matched
    if (numCompleted != instanceKey.size()) {
      continue;
    }
    
    //If user defined match function exists, check that.
    if (this->checkMatching) {
      if (!this->checkMatching(matchedInstances)) {
        continue;
      }
    }

    //Here I know I have a match in matchedInstances
    found = true;

    //Next steps are actually doing the replacement
    
    //TODO do I need to remove all internal connections first?
 
    //Add the replacement pattern (finally!!)
    string rName = replacement->getInstname()+c->getUnique();
    Args rConfigargs;
    if (this->getConfigArgs) {
      rConfigargs = this->getConfigArgs(matchedInstances);
    }
    else if (this->configargs.size()>1) {
      rConfigargs = this->configargs;
    }
    Instance* rinst = cdef->addInstance(rName,replacement,rConfigargs);
    
    //For each matched instance...
    for (uint i=0; i<instanceKey.size()) {
      Instance* minst = matchedInstances[i];
      assert(usedInstances.count(minst)==0);
      usedInstances.insert(minst);

      //Make a passthrough for the instance
      string ptName = "_pt" + c->getUnique();
      Instance* pt = addPassthrough(minst,ptName);
      passthroughsToInline.push_back(pt);
      
      //Use external connections to connect to replacement
      for (auto excon : exCons[i]) {
        SelectPath localPath = excon.first;
        SelectPath replacePath = excon.second;
        
        //ptName."in".localpath
        localPath.push_front("in");
        localPath.push_front(ptName);
  
        //rName.replacePath
        replacePath.push_front(rName);
        
        //Add the connection back to the cdef
        cdef->connect(localPath,replacePath);
      }

    }
  }

  //Now delete all the matched instances
  for (auto inst : usedInstances) {
    cdef->removeInstance(inst);
  }
 
  //Now inline all the passthrough Modules
  for (auto selstr : passthroughsToInline) {
    inlineInstance(cast<Instance>(cdef->sel(selstr)));
  }
  //TODO check if this should have removed any stray internal wires
  
  cdef->validate();
  return found;
}
