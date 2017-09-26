#include "coreir.h"

using namespace CoreIR;

int main() {

  Context* c = newContext();
  Namespace* global = c->getGlobal();

  //Now lets make our counter as a generator.
  //We want our Generator to be able to take in the parameter width.
  //We need to specify that the width is of type "int"
  Params counterParams({{"width",AINT}}); //"Arg Int". I know, its bad
  //Other param types: ABOOL,ASTRING,ATYPE

  //Instead of defining a type, now we need to define a type Generator. This allows CoreIR to statically type check all connections.
  TypeGen* counterTypeGen = global->newTypeGen(
    "CounterTypeGen", //name of typegen
    counterParams, //Params required for typegen
    [](Context* c, Args args) { //lambda for generating the type
      Arg* widthArg = args.at("width"); //Checking for valid args is already done for you
      uint width = widthArg->get<int>(); //get function to extract the arg value.
      return c->Record({
        {"en",c->BitIn()}, 
        {"out",c->Array(width,c->Bit())}, //Note: Array is parameterized by width now
        {"clk",c->Named("coreir.clkIn")},
      });
    } //end lambda
  ); //end newTypeGen
  ASSERT(global->hasTypeGen("CounterTypeGen"),"Can check for typegens in namespaces");


  //Now lets create a generator declaration for our counter
  Generator* counter = global->newGeneratorDecl("counter",counterTypeGen,counterParams);
  //The third argument is the counter parameters. This needs to be a superset of the parameters for the typegen.
  
  //Now lets define our generator function. I am going to use a lambda again, but you could pass in
  //  a normal function with the same type signature.
  counter->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
    //ModuleDef* def : The circuit you are defining.
    //Type* t: The generated Type of the counter (Using your counterTypeGen function!)
    //Args args: The arguments supplied to the instance of the counter.
    
    //Similar to the typegen, lets extract the width;
    uint width = args.at("width")->get<int>();
      
    //Now just define the counter with with all the '16's replaced by 'width'
    Args wArg({{"width",c->argInt(width)}});
    def->addInstance("ai","coreir.add",wArg);
    def->addInstance("ci","coreir.const",wArg,{{"value",c->argInt(1)}});
    //Reg has default arguments. en/clr/rst are False by default. Init is also 0 by default
    def->addInstance("ri","coreir.reg",{{"width",c->argInt(width)},{"en",c->argBool(true)}});
    
    //Connections
    def->connect("self.clk","ri.clk");
    def->connect("self.en","ri.en");
    def->connect("ci.out","ai.in0");
    def->connect("ai.out","ri.in");
    def->connect("ri.out","ai.in1");
    def->connect("ri.out","self.out");
  }); //end lambda, end function

  //Now lets test this by instancing a few counters.
  Module* tb = global->newModuleDecl("counterTestBench",c->Record({})); //empty record means no ports
  ModuleDef* tbdef = tb->newModuleDef();
    
    tbdef->addInstance("c0","global.counter",{{"width",c->argInt(17)}});
    tbdef->addInstance("c1","global.counter",{{"width",c->argInt(23)}});
    tbdef->connect("c0.out.16","c1.en"); //Connect bit 16 of counter 0 to en of counter 23
  
  tb->setDef(tbdef);
  
  counter->print();
  tb->print();
  
  //Lets find the instance called "c0"
  ASSERT(tbdef->getInstances().count("c0"),"This should have the instance!");
  //getInstances is just an unordered_map<string,Instance*>
  Instance* c0 = tbdef->getInstances()["c0"];
  
  //Lets get the Generator that the Instance is referencing (which thing was just instanced)
  Generator* c0GenRef = c0->getGeneratorRef();
  ASSERT(c0GenRef == counter,"This should be the Counter!");
  
  //Now lets run the generator
  c->runPasses({"rungenerators"});
  
  //We can assume that we have a pass that runs all generators (recursively)
  //Learn more about passes in the WritingPasses tutorial.
  
  //Lets check to see what the generators generated!
  
  //Lets get the Generator/Module that c0 is refencing again.
  Instantiable* c0InstantiableRef = c0->getInstantiableRef();

  //This time we are going to use the more generic getInstantiableRef.
  //As a reminder Instantiable is the parent class of both Generators and Modules. 
  //An Instantiable is something that can be instanced in a circuit.

  //Since the generator was run, c0 should now be referring to the generated module instead of a generator
  ASSERT(isa<Module>(c0InstantiableRef),"c0 is now referring to a module!");

  //There are three convenient casting-related functions for use in CoreIR. isa<T>, cast<T>, and dyn_cast<T>
  //You can learn more about those in doc/TODO.md
  Module* c0ModRef = cast<Module>(c0InstantiableRef);

  cout << "Printing the generated module!" << endl;
  c0ModRef->print();  

  //Lets make sure that width has correctly been propegated
  Type* c0ModType = c0ModRef->getType();
  //Cast to a recordtype
  if (RecordType* rt = dyn_cast<RecordType>(c0ModType)) {
    //Lets Make sure that the prot "out" exists
    ASSERT(rt->getRecord().count("out"),"Can get the map of fields to Types using getRecord");

    ArrayType* at = cast<ArrayType>(rt->getRecord()["out"]); //If I know the type for sure, use cast instead of dyn_cast
    ASSERT(at->getLen()==17,"Width correctly propogated through!");
    ASSERT(at->getElemType()==c->Bit(),"Can also get the Element Type of the Array");
  }
  else {
    ASSERT(0,"Modules should always have a record type!");
  }
  
  //Now lets actually save this to a real file.
  //Specify the namespace to save (global), the filename, and an optional "top" module
  saveToFilePretty(global,"counters.json",tb);

  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
