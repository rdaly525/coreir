#include "coreir.h"

using namespace CoreIR;

int main() {
  
  //Declare a new context for this program. This is where namespaces and types are stored. It also performs basic memory management. 
  Context* c = newContext();

  //Our goal is to define a counter module
  // first we need a type. This represents the interface to the counter module.
  // Our counter will have an "en", "clk" and "out" port
  // Types can be Bit, BitIn, Array, Record, or Named. 
  // All Modules should have a Reocrd type of the ports. So lets define that below
  Type* CounterType = c->Record({
    {"en",c->BitIn()}, //en is declared as a single BitIn
    {"out",c->Array(16,c->Bit())}, //Out is declared as An Array of 16 Bits (with directionality 'Out')
    {"clk",c->Named("coreir.clkIn")}, //Named types are customly named types. This particular one is just a wrapper of a BitIn type and represents a clock input
  });
  
  //Context has constructors for all basic types (Bit,BitIn, Array, Record, Named)
  //Note that the direction is specified at the "leaf" nodes of the type hierarchy (Bit, BitIn)

  //Every context comes with an empty "global" namespace
  //Namespaces contain Modules, Generators, and NamedTypes
  Namespace* global = c->getNamespace("global");
  
  //Now lets create a module. This is like a software function. It has a name and a type signature represented by the Type that we just created.
  Module* counter = global->newModuleDecl("counter",CounterType);

  //we now have a module that has a well defined interface, but no definition. Lets now create the coudefinition. The defintion will simply be a graph of instances and connections.
  ModuleDef* counterDef = counter->newModuleDef();
    
    //The counter definition of our counter will simply be a register with an add of the register output and the constant 1 driving the input of the register
    //We are now going to add all the instances (nodes). An Instance is simply an instance of a particular module.
    //We can use 'counterDef' to add Instances and add Connections.
    
    //We can find the add in the 'coreir' namespace. This namespace contains all of the coreir primitives. All of these primitives require a 'width' parameter.
    Values widthArg({{"width",Const::make(c,16)}});
    counterDef->addInstance("ai","coreir.add",widthArg);
    //We just created an instance of a coreir.add named 'ai'
    
    //Now lets add a constant 1. Along with the width arg, we also need to give the const a value of 1. the 16 is required because the size of the constant is 16 bits. 
    counterDef->addInstance("ci","coreir.const",widthArg,{{"value",Const::make(c,16,1)}});

    //Finally, lets add the register. This register is in a primitive extension namespace called mantle. this mantle register has the option of adding an 'en' port to its inteface.
    //This also requires an additional parameter called 'init' which represents the initial value of the register which we will set to 0.
    counterDef->addInstance(
      "ri",
      "mantle.reg",
      {{"width",Const::make(c,16)},{"has_en",Const::make(c,true)}},
      {{"init",Const::make(c,16,0)}}
    );
    
    //Lets now do all the connections. We can directly use the interface <instance_name>.<port_name> to connect instances together.
    //'self' is referencing the ports of the current module we are defining. The ports of 'self' should exactly match the type we just defined above (CounterType)
    counterDef->connect("self.clk","ri.clk");
    counterDef->connect("self.en","ri.en");
    counterDef->connect("ci.out","ai.in0");
    counterDef->connect("ai.out","ri.in");
    counterDef->connect("ri.out","ai.in1");
    counterDef->connect("ri.out","self.out");

  //We now need to specify that this definition that we just implemented should be attached to the counter module.
  counter->setDef(counterDef);

  //Now we can pretty print what we just created. Later tutorials will show more compilation options.
  counter->print();
  
  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
