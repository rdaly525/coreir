#include "coreir/ir/casting/casting.h"
#include "coreir/ir/context.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"

using namespace std;

namespace CoreIR {

// This helper will connect everything from wa to wb with a spDelta. 
// spDelta is the SelectPath delta to get from wa to wb
void connectOffsetLevel(ModuleDef* def, Wireable* wa, SelectPath spDelta, Wireable* wb) {
  
  for (auto waCon : wa->getConnectedWireables() ) {
    for (auto wbCon : wb->getConnectedWireables() ) { //was inw
      SelectPath wbConSPath = wbCon->getSelectPath();
      SelectPath waConSPath = waCon->getSelectPath();
      
      //concatenate the spDelta into wa
      waConSPath.insert(waConSPath.end(),spDelta.begin(),spDelta.end());
      def->connect(waConSPath,wbConSPath);
    }
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

  //cout << "Connecting same level" << endl;

  //wa should be the flip type of wb
  assert(wa->getType()==wb->getType()->getFlipped());
  
  auto waSelects = wa->getSelects();
  auto wbSelects = wb->getSelects();
  
  unordered_set<string> both;
  for (auto waSelmap : waSelects) {
    if (wbSelects.count(waSelmap.first)>0) {
      both.insert(waSelmap.first);
    }
  }

  //Traverse another same level for both
  for (auto selstr : both ) {
    connectSameLevel(def,waSelects[selstr],wbSelects[selstr]);
  }
  
  //Connect wb to all the subselects of wa
  for (auto spair : waSelects) {
    connectOffsetLevel(def,wb, {spair.first}, spair.second);
  }

  //Connect wa to all the subselects of wb
  for (auto spair : wbSelects) {
    connectOffsetLevel(def,wa, {spair.first}, spair.second);
  }

  //cout << "Connecting possible N^2 wireables" << endl;

  //Now connect all N^2 possible connections for this level
  for (auto waCon : wa->getConnectedWireables() ) {
    for (auto wbCon : wb->getConnectedWireables() ) {
      def->connect(waCon,wbCon);
    }
  }

  //cout << "Done connecting wireables" << endl;
}

namespace {
void PTTraverse(ModuleDef* def, Wireable* from, Wireable* to) {
  for (auto other : from->getConnectedWireables()) {
    def->connect(to,other);
  }
  vector<Wireable*> toDelete;
  for (auto other : from->getConnectedWireables()) {
    toDelete.push_back(other);
  }
  for (auto other : toDelete) {
    def->disconnect(from,other);
  }
  for (auto sels : from->getSelects()) {
    PTTraverse(def,sels.second,to->sel(sels.first));
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
    wcheck = wchecksel->getParent();
    ASSERT(wcheck->getConnectedWireables().size()==0,"Cannot add a passthrough to a wireable with connected selparents");
  }
  ModuleDef* def = w->getContainer();
  Type* wtype = w->getType();
  
  //Add actual passthrough instance
  Instance* pt = def->addInstance(instname,c->getGenerator("_.passthrough"),{{"type",Const::make(c,wtype)}});
  
  unordered_set<Wireable*> completed;
  PTTraverse(def,w,pt->sel("out"));
  
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

void saveSymTable(json& symtable,string path, Wireable* w) {
  if (w->getConnectedWireables().size()==0) {
    for (auto spair : w->getSelects()) {
      saveSymTable(symtable,path + "." + spair.first,spair.second);
    }
  }
  else {
    Wireable* other = *(w->getConnectedWireables().begin());
    assert(other);
    bool check = symtable.get<map<string,json>>().count(path)==0;
    ASSERT(check,"DEBUGME");
    symtable[path] = other->getSelectPath();
  }
}

//This will modify the moduledef to inline the instance
bool inlineInstance(Instance* inst) {
  Context* c = inst->getContext();
  //Special case for a passthrough
  //TODO should have a better check for passthrough than string compare
  Module* mref = inst->getModuleRef();
  if (mref->isGenerated() && mref->getGenerator()->getRefName() == "_.passthrough") {
    //cout << "Inlining: " << toString(inst) << endl;
    inlinePassthrough(inst);
    return true;
  }
  
  Values instModArgs = inst->getModArgs();
  ModuleDef* def = inst->getContainer();
  Module* modInline = mref;

  if (!modInline->hasDef()) {
    //cout << "Inline Pass: " << modInline->getName() << " has no definition, skipping..." << endl;;
    return false;
  }
  string instname = inst->getInstname();

  //Add a bunch of symbol table metadata
  //First for each port of instance that is connected
  //Save that as metadata (inst.port.blah -> its connection)
  json jsym(json::value_t::object);
  if (c->hasSymtable()) {
    saveSymTable(jsym,instname,inst);
  }

  //I will be inlining defInline into def
  //Making a copy because i want to modify it first without modifying all of the other instnaces of modInline
  ModuleDef* defInline = modInline->getDef()->copy();

  //Add a passthrough Module to quarentine 'self'
  addPassthrough(defInline->getInterface(),"_insidePT");
  
  string inlinePrefix = inst->getInstname() + "$";

  //First add all the instances of defInline into def with a new name
  for (auto instpair : defInline->getInstances()) {
    string iname = inlinePrefix + instpair.first;
    Values modargs = instpair.second->getModArgs();
    //Should do this in a more generic way
    for (auto vpair : modargs) {
      if (Arg* varg = dyn_cast<Arg>(vpair.second)) {
        ASSERT(instModArgs.count(varg->getField()),"DEBUG ME");
        modargs[vpair.first] = instModArgs[varg->getField()];
      }
    }
    def->addInstance(iname,instpair.second->getModuleRef(),modargs);
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
  // WARNING: Temporarily removed to check performance impact in _stereo.json
  //def->validate();
  
  if (c->hasSymtable()) {
    //for each entry in instances symbtable
    //prepend instname to key
    //determine where new instance is pointing to
    if (mref->getMetaData().get<map<string,json>>().count("symtable")) {
      json jisym = mref->getMetaData()["symtable"];
      for (auto p : jisym.get<map<string,json>>()) {
        string newkey = instname + "$" + p.first;
        
        ASSERT(jsym.count(newkey)==0,"DEBUGME");
        SelectPath path = p.second.get<SelectPath>();
        if (path[0] =="self") {
          path[0] = instname;
        }
        else {
          path[0] = inlinePrefix + path[0]; 
        }
        jsym[newkey] = path;
      }
    }
   
    if (def->getModule()->getMetaData().get<map<string,json>>().count("symtable")) {
      json jmerge = def->getModule()->getMetaData()["symtable"];
      for (auto pair : jsym.get<map<string,json>>()) {
        bool check = jmerge.get<map<string,json>>().count(pair.first)==0;
        ASSERT(check,"DEBUGME");
        jmerge[pair.first] = pair.second;
      }
      def->getModule()->getMetaData()["symtable"] = jmerge;
    }
    else {
      def->getModule()->getMetaData()["symtable"] = jsym;
    }
  } 


  return true;
}

}
  
