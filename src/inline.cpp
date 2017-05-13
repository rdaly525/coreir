
#include "wireable.hpp"

using namespace CoreIR;


// This helper will connact everything from w to inw. 
// spDelta is the SelectPath delta to get from w to inw
void connectAll_inwsel(ModuleDef* def, string inlinePrefix, Wireable* w, SelectPath spDelta, Wireable* inw) {
  //cout << "w:" << w->toString() << endl;
  //cout << "spDelta:" << SelectPath2Str(spDelta) << endl;
  //cout << "inw:" << inw->toString() << endl << endl;
  
  for (auto wOther : w->getConnectedWireables() ) {
    for (auto inwOther : inw->getConnectedWireables() ) {
      SelectPath inwOtherSPath = inwOther->getSelectPath();
      inwOtherSPath[0] = inlinePrefix + "$" + inwOtherSPath[0];
      SelectPath wOtherSPath = wOther->getSelectPath();
      //concatenate the spDelta
      wOtherSPath.insert(wOtherSPath.end(),spDelta.begin(),spDelta.end());
      def->connect(wOtherSPath,inwOtherSPath);
      //cout << "Hconnecting: " << SelectPath2Str(wOtherSPath) + " <==> " + SelectPath2Str(inwOtherSPath) << endl;
    }
  }

  //Traverse up the w
  if (auto ws = dyn_cast<Select>(w)) {
    SelectPath tu = spDelta;
    assert(ws->getParent());
    tu.insert(tu.begin(),ws->getSelStr());
    connectAll_inwsel(def,inlinePrefix,ws->getParent(),tu,inw);
  }

  //Traverse down the inw
  for (auto inwselmap : inw->getSelects()) {
    SelectPath td = spDelta;
    td.push_back(inwselmap.first);
    connectAll_inwsel(def,inlinePrefix,w,td,inwselmap.second);
  }
}

// This helper will connact everything from inw to w 
// spDelta is the SelectPath delta to get from inw to w
void connectAll_wsel(ModuleDef* def, string inlinePrefix, Wireable* w, SelectPath spDelta, Wireable* inw) {
  //cout << "w:" << w->toString() << endl;
  //cout << "spDelta:" << SelectPath2Str(spDelta) << endl;
  //cout << "inw:" << inw->toString() << endl << endl;
  for (auto wOther : w->getConnectedWireables() ) {
    for (auto inwOther : inw->getConnectedWireables() ) {
      SelectPath inwOtherSPath = inwOther->getSelectPath();
      inwOtherSPath[0] = inlinePrefix + "$" + inwOtherSPath[0];
      SelectPath wOtherSPath = wOther->getSelectPath();
      //concatenate the spDelta
      inwOtherSPath.insert(inwOtherSPath.end(),spDelta.begin(),spDelta.end());
      def->connect(wOtherSPath,inwOtherSPath);
      //cout << "Hconnecting: " << SelectPath2Str(wOtherSPath) + " <==> " + SelectPath2Str(inwOtherSPath) << endl;
    }
  }

  //Traverse up the inw
  if (auto inws = dyn_cast<Select>(inw)) {
    SelectPath tu = spDelta;
    tu.insert(tu.begin(),inws->getSelStr());
    connectAll_wsel(def,inlinePrefix,w,tu,inws->getParent());
  }

  //Traverse down the w
  for (auto wselmap : w->getSelects()) {
    SelectPath td = spDelta;
    td.push_back(wselmap.first);
    connectAll_wsel(def,inlinePrefix,wselmap.second,td,inw);
  }
}

//This helper will connect a single select layer at the inline interface boundary
void connectBoundary(ModuleDef* def, string inlinePrefix, Wireable* w, Wireable* inw) {
  auto wSelects = w->getSelects();
  auto inwSelects = inw->getSelects();
  
  //Sort into the three sets of the vendiagram
  unordered_set<string> wOnly;
  unordered_set<string> inwOnly;
  unordered_set<string> both;
  for (auto wsel : wSelects) {
    if (inwSelects.count(wsel.first)>0) {
      both.insert(wsel.first);
    }
    else {
      wOnly.insert(wsel.first);
    }
  }
  for (auto inwsel : inwSelects) {
    if (both.count(inwsel.first) == 0) {
      inwOnly.insert(inwsel.first);
    }
  }
  //auto setprint = [](unordered_set<string> s, string n) {
  //  cout << n << ": {";
  //  for (auto str : s) cout << str << ", ";
  //  cout << "}\n";
  //};
  //cout << w->toString() << endl;
  //setprint(wOnly, "wOnly");
  //setprint(inwOnly, "inwOnly");
  //setprint(both, "both");

  //Basic set theory assertion
  assert(wOnly.size() + inwOnly.size() + 2*both.size() == wSelects.size() + inwSelects.size());

  //Traverse another level for both
  for (auto selstr : both ) {
    connectBoundary(def, inlinePrefix, wSelects[selstr],inwSelects[selstr]);
  }
  
  //Connect all the subselects of inwOnly
  for (auto selstr : inwOnly) {
    connectAll_inwsel(def,inlinePrefix,w, {selstr}, inwSelects[selstr]);
  }

  //Connect all the subselects of wOnly
  for (auto selstr : wOnly) {
    connectAll_wsel(def,inlinePrefix,wSelects[selstr], {selstr}, inw);
  }

  //Now connect all N^2 possible connections for this level
  for (auto wOther : w->getConnectedWireables() ) {
    for (auto inwOther : inw->getConnectedWireables() ) {
      SelectPath inwOtherSPath = inwOther->getSelectPath();
      inwOtherSPath[0] = inlinePrefix + "$" + inwOtherSPath[0];
      def->connect(wOther->getSelectPath(),inwOtherSPath);
      //cout << "connecting: " << SelectPath2Str(wOther->getSelectPath()) + " <==> " + SelectPath2Str(inwOtherSPath) << endl;
    }
  }
}


//This will modify the moduledef to inline the instance
void Instance::inlineModule() {
  Instance* inst = this;
  ModuleDef* def = inst->getModuleDef();
  Module* modInline = inst->getModuleRef();
  if (!modInline->hasDef()) {
    cout << "Cannot inline a module with no definition!: " << modInline->getName() << endl;
    return;
  }
  ModuleDef* defInline = modInline->getDef();
  string inlinePrefix = inst->getInstname();

  //I will be inlining defInline into def

  //First add all the instances of defInline into def. And add them to a map
  for (auto instmap : defInline->getInstances()) {
    string iname = inlinePrefix + "$" + instmap.first;
    def->addInstance(instmap.second,iname);
  }
  
  //Now add all the easy connections (that do not touch the boundary)
  for (auto cons : defInline->getConnections()) {
    SelectPath pA = cons.first->getSelectPath();
    SelectPath pB = cons.second->getSelectPath();
    
    //Easy case: when neither are connect to self
    if (pA[0] != "self" && pB[0] != "self") {
      //Create the correct names and connect
      pA[0] = inlinePrefix + "$" + pA[0];
      pB[0] = inlinePrefix + "$" + pB[0];
      def->connect(pA,pB);
    }
  }

  //Now connect All the hard ones at the boundary
  connectBoundary(def, inlinePrefix, inst, defInline->getInterface());

  //Now remove the instance (which should remove all the previous connections)
  def->removeInstance(inst->getInstname());

  //typecheck the module
  def->validate();
}
