
/*
 * Now we are going to write a more complicated pass using 
 * The InstanceGraph Pass API
 * This Pass is analogous to LLVM's CallGraphSCC pass.
 * InstanceGraph Passes run on InstanceGraphNodes in topologically sorted order (starting at leaves).
 * an InstanceGraphNode represents an instantaible + it's use-def structure. 
 * 
 * InstanceGraph Passes can make changes to the current Instantiable, or any
 * InstanceGraph which contains instances of it. There is an API for accessing these instances
 * as part of a sort of use-def tree.
 *
 * Another cool API this node supports is changing the Type of the current Instantiable you are in.
 * This can be dangerous, so lets see how to do this safely. 
 *
 * Lets make a pass that creates a global enable and wires it up to all the registers
 */

#include "coreir.h"
#include "coreir-macros.h"

//I made a copy of the hellmodule and embedded in the system. For external passes 
//referencing analysis passes, you need to add it to the full build.
#include "coreir/passes/analysis/hellomodule.h"

using namespace CoreIR;

//Start by inheriting from the predefined InstanceGraphPass
class HelloInstanceGraph : public InstanceGraphPass {
  
  //Lets define a name for our global_en. We will add this port to all modules needing it
  std::string globalEnName = "global_en";
  public:
    //The static keyword is important here!
    static std::string ID;
    //
    HelloInstanceGraph() : InstanceGraphPass(ID,"Descritpion Blah Blah",false) {}

    //Function that needs to be overrided
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;

    //This function allows users to set which analysis passes they expect to use.
    //The PassManager will guarantee that all dependent passes will be valid exactly before
    //The current pass is run. 
    void setAnalysisInfo() override {
      addDependency("hellomodule2");
    }
};

string HelloInstanceGraph::ID = "helloinstancegraph";
bool HelloInstanceGraph::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Context* c = this->getContext();
  Instantiable* i = node.getInstantiable();
  

  //Early out on Generators
  if (isa<Generator>(i)) return false;
  Module* m = cast<Module>(i);

  //Early out on module declarations
  if (!m->hasDef()) return false;

  ModuleDef* def = m->getDef();

  //Use getAnalysisPass template function to get access to the HelloModule pass.
  //Remember this will be guaranteed to run before your custom pass given the 
  //setAnalysisInfo
  Passes::HelloModule* hellomodule = this->getAnalysisPass<Passes::HelloModule>();
  
  Generator* coreir_and = c->getGenerator("coreir.and");
  
  //Structure to maintain where to wire global_en
  vector<Wireable*> toWire;

  //Now I can access the API I just defined in the previous example
  if (hellomodule->hasRegisterInstances(i)) {
    //If I have instances, I need to make sure they all have an enable.
    for (auto reginst : hellomodule->getRegisterInstances(i)) {
      
      //If already has an enable, need to add an and gate to it!
      if (cast<RecordType>(reginst->getType())->getRecord().count("en") ) {
        //Adding the and using passthrough magic (TODO explain better)
        Instance* andInst = def->addInstance("and" + c->getUnique(),coreir_and,{{"width",c->argInt(1)}});
        Instance* pt = addPassthrough(reginst,"_pt");
        def->disconnect(pt->sel("in"),reginst);
        def->connect(andInst->sel("out"),reginst->sel("en"));
        def->connect(pt->sel("in")->sel("en"),andInst->sel("in0"));
        toWire.push_back(andInst->sel("in1"));
        inlineInstance(pt);
      }
      else {
        ASSERT(0,"NYI, replace register with register with enable");
      }
    }
  }
  //Now check for other global_en ports and add to toWire list
  for (auto instmap : def->getInstances()) {
    Instance* inst = instmap.second;
    if (cast<RecordType>(inst->getType())->getRecord().count(globalEnName)) {
      Wireable* globalEn = inst->sel(globalEnName);
      //Can check whether it is connected to anything
      ASSERT(globalEn->getConnectedWireables().size()==0,"gloalEn is already connected!");

      //Add to list
      toWire.push_back(inst->sel(globalEnName));
    }
  }

  if (toWire.size() > 0) {
    //Need to add a global_en port to myself now
    //This is safe because I am not changing any connections
    node.appendField(globalEnName,c->BitIn());


    Wireable* selfGlobalEn = def->getInterface()->sel(globalEnName);
    
    //Now wire up everything
    for (auto w : toWire) {
      def->connect(w,selfGlobalEn);
    }
  }

  //Return if modified!
  return toWire.size() > 0;
}

//This is the macro that will define the registerPass and deletePass functions for you.
COREIR_GEN_EXTERNAL_PASS(HelloInstanceGraph);
