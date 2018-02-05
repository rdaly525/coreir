#include "coreir.h"

using namespace CoreIR;

int main() {

  //Declare a new context for this program. This is where namespaces and types are stored. It also performs basic memory management. 
  Context* c = newContext();

  //Every context comes with an empty "global" namespace
  //Namespaces countain Modules, Generators, and NamedTypes
  Namespace* global = c->getNamespace("global");
  ASSERT(global->getName() == "global","Get the namespace name!");

  //Every context also comes preloaded with 'coreir' namespace
  //coreir contains all of the primitives (like add, reg, and, etc)
  Namespace* coreir = c->getNamespace("coreir");
  Namespace* mantle = c->getNamespace("mantle");
 
  //Our goal is to define a counter module
  // first we need a type. This represents the interface to the counter module.
  // Our counter will have an "en", "clk" and "out" port
  // Types can be Bit, BitIn, Array, Record, or Named. 
  // All Modules should have a Reocrd type of the ports. So lets define that below

  Type* CounterType = c->Record({
    {"en",c->BitIn()}, //en is declared as a single BitIn
    {"out",c->Array(16,c->Bit())}, //Out is declared as An Array of 16 Bit (out)
    {"clk",coreir->getNamedType("clkIn")}, //Named types are customly named types defined in namespaces
  });

  //Context has constructors for all basic types (Bit,BitIn, Array, Record)
  //Namespace has constructors for Named types
  //Note that the direction is specified at the "leaf" nodes of the type hierarchy (Bit, BitIn)
  
  //Now lets create a module declaration. Declarations are specified separately from the definition
  Module* counter = global->newModuleDecl("counter",CounterType);
  ASSERT(counter->getType() == CounterType,"I can check for equality on types!");
  ASSERT(counter->getName() == "counter","I can get the name!");
  ASSERT(counter->getNamespace() == global,"I can get the namespace I am defined in!");
  ASSERT(global->hasModule("counter"),"I can check for modules in namespaces");

  //This gives us a handle to a defintion which is where we will be defining all our instances/connections
  ModuleDef* def = counter->newModuleDef();
  
  //Lets get all the modules/generators that we are going to use.
  //A counter requires an adder, a register and a constant(1)
  //Note all of the coreir primitives are generators because they require a width argument.
  Generator* Add = coreir->getGenerator("add");
  Generator* Reg = mantle->getGenerator("reg");
  Generator* Const = coreir->getGenerator("const");

  //Lets instance the Add and call it "ai"
  Instance* ai = def->addInstance("ai",Add,{{"width",Const::make(c,16)}});
  
  //The third value here is the genValues (generator arguments).
  //You specify all of the parameters required by the generator here.
  //a Generator Arg can be a bool, int, string or CoreIR::Type*
  //These each have correspondng constructors found in CoreIR::context.

  //Now lets instance the Constant.
  def->addInstance("ci",Const,{{"width",Const::make(c,16)}},{{"value",Const::make(c,16,1)}});

  //What is this 4th argument? This is a configarg. Configargs are usually things like initialization values 
  //Or anything that does not change the type or structure of the circuit. Constant has one config arg 
  //representing its value (in this case, 1).
  
  //And finally lets instance the Register
  //Lets specify all the arguments to the register separately
  Values regGenValues({
    {"width",Const::make(c,16)}, //width of the register
    {"has_en",Const::make(c,true)}, //Does the register have an enable port?
    {"has_clr",Const::make(c,false)}, //Does the register have a synchronous clr?
    {"has_rst",Const::make(c,false)} //Does the register have an asynchronous rst?
  });
  Values regConfigValues({{"init",Const::make(c,16,0)}}); //Initialiation value of the register
  Instance* ri = def->addInstance("ri",Reg,regGenValues,regConfigValues);

  //Now that we have the instances, lets specify the connections
  //Lets first specifiy the connection between the adder and the register.
  Wireable* ai_out = ai->sel("out");
  Wireable* ri_in = ri->sel("in");
  def->connect(ai_out, ri_in);
  
  //Lets break down what is happening here.
  //A Wireable is something that can be connected to. We can "select" any subtype of our instances by
  //using the select function. In this case I know that coreir.add has a port called "out" and 
  //coreir.reg has a port called "in", and that they have opposite (flipped) types.
  //ModuleDef.connect takes in two wireables and connects them together).
  //Wireables can only be connected together if one type is exactly the flip of the other.
  //Opposite types are defined to be the same exact type execpt for opposite directions in the hierarchical type leaf node.
  //BitIn can be connected to Bit
  //Array(16,Bit) can connect to Array(16,BitIn)
  //Record({a:BitIn,b:Bit}) can connect to Record({a:Bit,b:BitIn}) but not Record({a:Bit,b:BitIn,en:Bit})
  //Named(coreir.clkIn) can connect to Named(coreir.clk) but not to Bit

  //Now how do we connect to the Module's interface (ports)?
  Wireable* interface = def->getInterface();
  //Note: The interface represents the flip type of the Module type. 
  //So in this case the Type would be:
  Type* InterfaceType = c->Record({
    {"en",c->Bit()},
    {"out",c->Array(16,c->BitIn())},
    {"clk",c->Named("coreir.clk")},
  });
  ASSERT(interface->getType() == InterfaceType,"Interface is what I expect");
  ASSERT(interface->getType() == counter->getType()->getFlipped(),"Convenient Flip Type Constructor on types!");

  //So lets add the rest of the connections (a litle more succinctly)
  def->connect(interface->sel("en"), ri->sel("en"));
  def->connect(interface->sel("clk"), ri->sel("clk"));
  //Some syntax sugar
  def->connect({"ci","out"}, {"ai","in0"});
  //even more sugar
  def->connect("ri.out","ai.in1");
  def->connect("ri.out","self.out");
  //Note: 'self' is a reserved port name. You can use this to refer to the interface of the module

  //Now we have completed our definition. Lets set our module to use this definition.
  counter->setDef(def);

  //Now we can print it to see the pretty print of the module
  counter->print();
  
  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
