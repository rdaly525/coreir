
#include "wireable.hpp"

using namespace CoreIR;
//This helper will connect a single select layer at the inline interface boundary
void connectBoundary(ModuleDef* def, string inlinePrefix, Wireable* w, Wireable* inw) {
  auto wSelects = w->getSelects();
  auto inwSelects = inw->getSelects();
  
  //Sort into three sets
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
  auto setprint = [](unordered_set<string> s) {
    cout << "{";
    for (auto str : s) cout << str << ", ";
    cout << "}\n";
  };
  //setprint(wOnly);
  //setprint(inwOnly);
  //setprint(both);

  assert(wOnly.size() + inwOnly.size() + 2*both.size() == wSelects.size() + inwSelects.size());

  //Traverse another level for both
  for (auto selstr : both ) {
    connectBoundary(def, inlinePrefix, wSelects[selstr],inwSelects[selstr]);
  }
  
  //TODO Deal with wOnly and inwOnly
  ASSERT(wOnly.size()+inwOnly.size()==0,"NYI inlining with nested connections");
  
  //Now connect all N^2 possible connections for this level
  for (auto wOther : w->getConnectedWireables() ) {
    for (auto inwOther : inw->getConnectedWireables() ) {
      SelectPath inwOtherSPath = inwOther->getSelectPath();
      inwOtherSPath[0] = inlinePrefix + "&" + inwOtherSPath[0];
      def->connect(wOther->getSelectPath(),inwOtherSPath);
    }
  }
}

//This will modify the moduledef to inline the instance
void Instance::inlineModule() {
  Instance* inst = this;
  ModuleDef* def = inst->getModuleDef();
  Module* modInline = inst->getModuleRef();
  if (!modInline->hasDef()) {
    cout << "Cannot inline a module with no definition!" << endl;
    return;
  }
  ModuleDef* defInline = modInline->getDef();
  string inlinePrefix = inst->getInstname();

  //I will be inlining defInline into def

  //First add all the instances of defInline into def. And add them to a map
  for (auto instmap : defInline->getInstances()) {
    string iname = inlinePrefix + "&" + instmap.first;
    def->addInstance(instmap.second,iname);
  }
  
  //Now add all the easy connections (that do not touch the boundary)
  for (auto cons : defInline->getConnections()) {
    SelectPath pA = cons.first->getSelectPath();
    SelectPath pB = cons.second->getSelectPath();
    
    //Easy case: when neither are connect to self
    if (pA[0] != "self" && pB[0] != "self") {
      //Create the correct names and connect
      pA[0] = inlinePrefix + "&" + pA[0];
      pB[0] = inlinePrefix + "&" + pB[0];
      def->connect(pA,pB);
    }
  }

  //Now connect All the hard ones at the boundary
  connectBoundary(def, inlinePrefix, inst, defInline->getInterface());

  //Now remove the instance (which should remove all the previous connections
  def->removeInstance(inst->getInstname());
  def->validate();
}
