#include "coreir.h"

using namespace std;
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
 
  //We will define the Type by building up the RecordParams
  RecordParams counterTypeParams;
  counterTypeParams.push_back({"en",c->BitIn()});
  counterTypeParams.push_back({"out",c->Array(16,c->Bit())});
  counterTypeParams.push_back({"clk",coreir->getNamedType("clkIn")});
  Type* CounterType = c->Record(counterTypeParams);
  
  //Now lets create a module declaration. Declarations are specified separately from the definition
  Module* counter = global->newModuleDecl("counter",CounterType);
  ASSERT(counter->getType() == CounterType,"I can check for equality on types!");
  ASSERT(counter->getName() == "counter","I can get the name!");
  ASSERT(counter->getNamespace() == global,"I can get the namespace I am defined in!");
  ASSERT(global->hasModule("counter"),"I can check for modules in namespaces");

  //This gives us a handle to a defintion which is where we will be defining all our instances/connections
  ModuleDef* def = counter->newModuleDef();
  
  //Lets get all the modules/generators that we are going to use.
  //A counter requires an adder, a register and a constant
  //All of the primtiives of coreir are actuall generators. Generators are 'metafunctions' which take in a set of parameters and produce a module
  //Note all of the coreir primitives are generators because they require a width argument.
  //We can get the generator object from the namespace.
  Generator* addGen = coreir->getGenerator("add");
  Generator* constGen = coreir->getGenerator("const");

  //Our register, we are going to get from a different namespace called mantle. 
  //I can also just get the generator from the context directly by specifying the namespace "<namespace>.<generator_name>"
  Generator* regGen = c->getGenerator("mantle.reg");


  //To be explicit lets generate the module Add<width=16> which is created from the add generator.
  //This will only create the module, but *not* the definition for the Add<width=16> module. In fact, by default there is no definition for the Add primtive.
  Const* width16 = Const::make(c,16);
  Module* add16Mod = addGen->getModule({{"width",width16}});
  
  //Lets instance the Add16 and call it "ai"
  Instance* ai = def->addInstance("ai",add16Mod);
  
  //Note, the following two 'syntax sugar' calls could have been used instead of the above two statements
  //Instance* ai = def->addInstance("ai",addGen,{{"width",width16}});
  //Instance* ai = def->addInstance("ai","coreir.add",{{"width",width16}});
  
  //Before we instantiate the rest, lets discuss with the hell was the 'Const::make(c,16)'
  //This represents a 'boxed' constant Value that can be passed into generators. All generators requre a set of generator arguments to be passed into it. These are a sepcified set of typed 'meta' arguments. Each argument will have a required name and ValueType specified by the generator params. 
  Params addGenParams = addGen->getGenParams();
  ValueType* widthType = addGenParams["width"];
  //Slightly confusing, but ValueType is the 'type' of a Value. This is different than a Type which is the type of the module and represents the interface to the module. 
  
  //We can see that 'width' is required to be an Int. 
  ASSERT(widthType == c->Int(),"width has to be of type Int");
  //We can access the ValueType objects from the Context. These are singltons so you can directly compare values.
  //These can be: Bool, Int, String, BitVector, Type (remember this is the module type!), or even a Module
  
  //We can also see that our Const* width16 is of type Int, and has a value of 16
  ASSERT(width16->getValueType()==c->Int(),"The ValueType of width16 needs to be Int");
  ASSERT(width16->get<int>() == 16, "The actual value of the int is 16");

  //Const* width16 is actually a Value. We can check this 'is a' relationship using the isa<> function
  ASSERT(isa<Value>(width16),"ConstInt really is a Value");
  
  //We can also explicitly cast the ConstInt to be a Value.
  Value* width16_casted = cast<Value>(width16);
  cout << "We can toString a Value: " << width16_casted->toString() << endl;

  //Now lets instantiate the register with an initial value of '0' in our counter circuit.
  //We chose the mantle.reg because we have the option of specifiying whether we would like an 'en' input.
  Value* has_en = Const::make(c,true);
  Values reg16GenArgs = {{"width",width16}, {"has_en",has_en}};
  Module* reg16 = regGen->getModule(reg16GenArgs);

  //We can now see that our generated module will have an enable port
  ASSERT(reg16->getType()->getRecord().count("en"),"reg16 has an 'en' port!");
  
  
  //Now, unlike the add module, the reg16 module requires an argument called 'init' to be passed in.
  //We can see this by looking at the modparams of the module.
  Params requiredModParams = reg16->getModParams();
  ASSERT(requiredModParams.count("init"),"This Module requires the 'init' param");
  //Note the Params is simply just a c++ map<string,ValueType*>. To check if a key is in this map, you can use the count(string) function
  
  //The ValueType of this parameter is a BitVector<16>. This is because the register is exactly 16 bits wide, so the init constant has to be a 16-bit value.
  ASSERT(requiredModParams["init"] == c->BitVector(16),"init is a 16 bit bitvector");
  
  //Lets now create a 16-bit 0.
  BitVector bv16_0 = BitVector(16,0);
  
  //Now lets create a Const Value which contains the 'value' bv16_0
  Const* init16 = Const::make(c,bv16_0);
  //Note, I could have done this in one step by doing:
  //Const* init16 = Const::make(c,16,0);

  //Now lets create the arguments we will pass into reg16.
  Values reg16ModArgs = {{"init",init16}};

  //Now lets instance the register with our init value and call the instance 'ri'
  Instance* ri = def->addInstance("ri",reg16,reg16ModArgs);

  //And finally lets instance the constant 1 in our circuit.
  //Similar to how the register has a required modarg of 'init', the constant has a required modarg of 'value' which represents its actual value. We can create an instance all at once by passing in the instance name, the generator, the genArgs, and the modArgs
  def->addInstance(
      "ci", //The instance name
      constGen, //The Generator
      {{"width",Const::make(c,16)}}, //The generator arguments
      {{"value",Const::make(c,16,1)}} //The module arguments
  );

  //Now that we have the instances, lets specify the connections
  //Lets first specifiy the connection between the adder and the register.
  Wireable* ai_out = ai->sel("out");
  Wireable* ri_in = ri->sel("in");
  def->connect(ai_out, ri_in);
  
  //Lets break down what is happening here.
  //A Wireable is something that can be connected to. We can "select" any subtype of our instances by
  //using the select function. In this case I know that coreir.add has a port called "out" and 
  //mantle.reg has a port called "in", and that they have opposite (flipped) types.
  //ModuleDef.connect takes in two wireables and connects them together.
  //Wireables can only be connected together if one type is exactly the flip of the other.
  //Opposite types are defined to be the same exact type execpt for opposite directions in the hierarchical type leaf node.
  //BitIn can be connected to Bit
  //Array(16,Bit) can connect to Array(16,BitIn)
  //Record({a:BitIn,b:Bit}) can connect to Record({a:Bit,b:BitIn}) but not to Record({a:Bit,b:BitIn,en:Bit})
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
  
  //We can also verify that we have all the ports connected fully by running the following pass. 
  c->runPasses({"verifyconnectivity"});

  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
