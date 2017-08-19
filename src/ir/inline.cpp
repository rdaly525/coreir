
#include "coreir.h"

namespace CoreIR {

// This helper will connect everything from wa to wb with a spDelta. 
// spDelta is the SelectPath delta to get from wa to wb
void connectOffsetLevel(ModuleDef* def, Wireable* wa, SelectPath spDelta, Wireable* wb) {
  //cout << "w:" << w->toString() << endl;
  //cout << "spDelta:" << SelectPath2Str(spDelta) << endl;
  //cout << "inw:" << inw->toString() << endl << endl;
  
  for (auto waCon : wa->getConnectedWireables() ) {
    for (auto wbCon : wb->getConnectedWireables() ) { //was inw
      SelectPath wbConSPath = wbCon->getSelectPath();
      SelectPath waConSPath = waCon->getSelectPath();
      //concatenate the spDelta into wa
      waConSPath.insert(waConSPath.end(),spDelta.begin(),spDelta.end());
      def->connect(waConSPath,wbConSPath);
      //cout << "Hconnecting: " << SelectPath2Str(wOtherSPath) + " <==> " + SelectPath2Str(inwOtherSPath) << endl;
    }
  }

  //Traverse up the wa keeping wb constant
  if (auto was = dyn_cast<Select>(wa)) {
    SelectPath tu = spDelta;
    assert(was->getParent());
    tu.push_front(was->getSelStr());
    connectOffsetLevel(def,was->getParent(),tu,wb);
  }

  //Traverse down the wb keeping wa constant
  for (auto wbselmap : wb->getSelects()) {
    SelectPath td = spDelta;
    td.push_back(wbselmap.first);
    connectOffsetLevel(def,wa,td,wbselmap.second);
  }
}

//This helper will connect a single select layer of the passthrough.
void connectSameLevel(ModuleDef* def, Wireable* wa, Wireable* wb) {
  
  //wa should be the flip type of wb
  assert(wa->getType()==wb->getType()->getFlipped());
  
  auto waSelects = wa->getSelects();
  auto wbSelects = wb->getSelects();
  
  //Sort into the three sets of the vendiagram
  unordered_set<string> waOnly;
  unordered_set<string> wbOnly;
  unordered_set<string> both;
  for (auto waSelmap : waSelects) {
    if (wbSelects.count(waSelmap.first)>0) {
      both.insert(waSelmap.first);
    }
    else {
      waOnly.insert(waSelmap.first);
    }
  }
  for (auto wbSelmap : wbSelects) {
    if (both.count(wbSelmap.first) == 0) {
      wbOnly.insert(wbSelmap.first);
    }
  }

  //Basic set theory assertion
  assert(waOnly.size() + wbOnly.size() + 2*both.size() == waSelects.size() + wbSelects.size());

  //Traverse another level for both
  for (auto selstr : both ) {
    connectSameLevel(def,waSelects[selstr],wbSelects[selstr]);
  }
  
  //TODO check any bugs here first
  //Connect wb to all the subselects of waOnly
  for (auto selstr : waOnly) {
    connectOffsetLevel(def,wb, {selstr}, waSelects[selstr]);
  }

  //Connect wa to all the subselects of wbOnly
  for (auto selstr : wbOnly) {
    connectOffsetLevel(def,wa, {selstr}, wbSelects[selstr]);
  }

  //Now connect all N^2 possible connections for this level
  for (auto waCon : wa->getConnectedWireables() ) {
    for (auto wbCon : wb->getConnectedWireables() ) {
      def->connect(waCon,wbCon);
      //cout << "connecting: " << SelectPath2Str(wOther->getSelectPath()) + " <==> " + SelectPath2Str(inwOtherSPath) << endl;
    }
  }
}

//addPassthrough will create a passthrough Module for Wireable w with name <name>
  //This buffer has interface {"in": Flip(w.Type), "out": w.Type}
  // There will be one connection connecting w to name.in, and all the connections
  // that originally connected to w connecting to name.out which has the same type as w
Instance* addPassthrough(Wireable* w,string instname) {
  
  //First verify if I can actually place a passthrough here
  //This means that there can be nothing higher in the select path tha is connected
  Context* c = w->getContext();
  Wireable* wcheck = w;
  while (Select* wchecksel = dyn_cast<Select>(wcheck)) {
    Wireable* wcheck = wchecksel->getParent();
    ASSERT(wcheck->getConnectedWireables().size()==0,"Cannot add a passthrough to a wireable with connected selparents");
  }
  
  ModuleDef* def = w->getContainer();
  Type* wtype = w->getType();
  
  //Add actual passthrough instance
  Instance* pt = def->addInstance(instname,c->getGenerator("coreir.passthrough"),{{"type",c->argType(wtype)}});
  
  LocalConnections cons = w->getLocalConnections();
  for (auto con : cons) {
    cout << "  " << Connection2Str(Connection(con.first,con.second)) << endl;
    SelectPath curPath = con.first->getSelectPath();
    curPath[0] = "out";
    curPath.push_front(instname);
    SelectPath otherPath = con.second->getSelectPath();
    def->connect(curPath,otherPath);
    def->disconnect(con.first,con.second);
  }
  
  //Connect the passthrough back to w
  def->connect(w,pt->sel("in"));

  return pt;
}

//This will inline an instance of a passthrough
void inlinePassthrough(Instance* i) {
  
  ModuleDef* def = i->getContainer();

  //This will recursively connect all the wires together
  connectSameLevel(def, i->sel("in"),i->sel("out"));

  //Now delete this instance
  def->removeInstance(i);
}


//This will modify the moduledef to inline the instance
bool inlineInstance(Instance* inst) {
  //Special case for a passthrough
  //TODO should have a better check for passthrough than string compare
  if (inst->isGen() && inst->getGeneratorRef()->getName() == "passthrough") {
    inlinePassthrough(inst);
    return true;
  }
  if (inst->isGen()) {
    return false;
  }
  ModuleDef* def = inst->getContainer();
  Module* modInline = inst->getModuleRef();
  assert(modInline);

  if (!modInline->hasDef()) {
    cout << "Cannot inline a module with no definition!: " << modInline->getName() << endl;
    return false;
  }
  
  //I will be inlining defInline into def
  //Making a copy because i want to modify it first without modifying all of the other instnaces of modInline
  ModuleDef* defInline = modInline->getDef()->copy();

  //Add a passthrough Module to quarentine 'self'
  addPassthrough(defInline->getInterface(),"_insidePT");

  string inlinePrefix = inst->getInstname() + "$";

  //First add all the instances of defInline into def with a new name
  for (auto instmap : defInline->getInstances()) {
    string iname = inlinePrefix + instmap.first;
    def->addInstance(instmap.second,iname);
  }
  
  //Now add all the easy connections (that do not touch the boundary)
  for (auto cons : defInline->getConnections()) {
    SelectPath pA = cons.first->getSelectPath();
    SelectPath pB = cons.second->getSelectPath();
    
    //Easy case: when neither are connect to self
    if (pA[0] != "self" && pB[0] != "self") {
      //Create the correct names and connect
      pA[0] = inlinePrefix + pA[0];
      pB[0] = inlinePrefix + pB[0];
      def->connect(pA,pB);
    }
  }
  
  //Create t3e Passthrough to quarentene the instance itself
  Instance* outsidePT = addPassthrough(inst,"_outsidePT");

  //Connect the two passthrough buffers together ('in' ports are facing the boundary)
  def->connect("_outsidePT.in",inlinePrefix + "_insidePT.in");

  //Now remove the instance (which will remove all the previous connections)
  def->removeInstance(inst);
  
  //Now inline both of the passthroughs
  inlineInstance(outsidePT);
  
  inlineInstance(cast<Instance>(def->sel(inlinePrefix + "_insidePT")));

  //typecheck the module
  def->validate();
  return true;
}

}
  
