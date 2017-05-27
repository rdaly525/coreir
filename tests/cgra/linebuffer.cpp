#include "coreir.h"
#include "coreir-lib/cgralib.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.h"


using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Put linebuffer in the cgra namespace
  Namespace* g = CoreIRLoadLibrary_cgralib(c);
  CoreIRLoadLibrary_stdlib(c);

  //Declare a TypeGenerator (in global) for linebuffer
  g->newTypeGen(
    "linebuffer_type", //name for the typegen
    {{"stencil_width",AINT},{"stencil_height",AINT},{"image_width",AINT},{"bitwidth",AINT}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
      uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
      //uint image_width = args.at("image_width")->get<ArgInt>();
      uint bitwidth = args.at("bitwidth")->get<ArgInt>();
      return c->Record({
	  {"in",c->BitIn()->Arr(bitwidth)},
	  {"out",c->Bit()->Arr(bitwidth)->Arr(stencil_height)->Arr(stencil_width)}
      });
    }
  );


  Generator* linebuffer = g->newGeneratorDecl("linebuffer",
					      g->getTypeGen("linebuffer_type"),
					      {{"stencil_width",AINT},{"stencil_height",AINT},
					       {"image_width",AINT},{"bitwidth",AINT}});
  
  linebuffer->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
    uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
    uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
    uint image_width = args.at("image_width")->get<ArgInt>();
    uint bitwidth = args.at("bitwidth")->get<ArgInt>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_height > 1);
    assert(stencil_width > 0);
    assert(image_width > stencil_width);
    assert(bitwidth > 0);

    Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
    Generator* Mem = cgralib->getGenerator("Mem");
    Generator* Reg = cgralib->getGenerator("Reg");
    Arg* aBitwidth = c->argInt(bitwidth);
    Arg* aImageWidth = c->argInt(image_width);

    // create the inital register chain
    std::string reg_prefix = "reg_";
    for (uint j = 0; j < stencil_width; ++j) {

      std::string reg_name = reg_prefix + "0_" + std::to_string(j);
      def->addInstance(reg_name, Reg, {{"width",aBitwidth}});
      
      // connect the input
      if (j == 0) {
	def->connect({"self","in"}, {reg_name, "in"});
      } else {
	std::string prev_reg = reg_prefix + "0_" + std::to_string(j-1);
	def->connect({prev_reg, "out"}, {reg_name, "in"});
      }
    }

    // connect together the memory lines
    std::string mem_prefix = "mem_";
    for (uint i = 1; i < stencil_height; ++i) {
      std::string mem_name = mem_prefix + std::to_string(i);
      def->addInstance(mem_name,Mem,{{"width",aBitwidth},{"depth",aImageWidth}},{{"mode",c->argString("o")}});

      // connect the input
      if (i == 1) {
	def->connect({"self","in"}, {mem_name, "wdata"});
      } else {
	std::string prev_mem = mem_prefix + std::to_string(i-1);
	def->connect({prev_mem, "rdata"}, {mem_name, "wdata"});
      }
    }

    // connect together the remaining stencil registers
    for (uint i = 1; i < stencil_height; ++i) {
      for (uint j = 0; j < stencil_width; ++j) {
	std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
	def->addInstance(reg_name, Reg, {{"width",aBitwidth}});
	
	// connect the input
	if (j == 0) {
	  std::string mem_name = mem_prefix + std::to_string(i);
	  def->connect({mem_name, "rdata"}, {reg_name, "in"});
	} else {
	  std::string prev_reg = reg_prefix + std::to_string(i) + "_" + std::to_string(j-1);
	  def->connect({prev_reg, "out"}, {reg_name, "in"});
	}
      }
    }

    // connect the stencil outputs
    for (uint i = 0; i < stencil_height; ++i) {
      for (uint j = 0; j < stencil_width; ++j) {
	std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
	def->connect({reg_name, "out"}, {"self","out",std::to_string(i),std::to_string(j)});
      }
    }    

  });

  // Define lb33 Module
  Type* lb33Type = c->Record({
    {"in",c->BitIn()->Arr(16)},
    {"out",c->Bit()->Arr(16)->Arr(3)->Arr(3)}
  });


  Module* lb33 = c->getGlobal()->newModuleDecl("lb33", lb33Type);
  ModuleDef* def = lb33->newModuleDef();
    def->addInstance("lb33_inst", linebuffer, {{"bitwidth",c->argInt(16)},
	  {"stencil_width",c->argInt(3)},{"stencil_height",c->argInt(3)},
					   {"image_width",c->argInt(512)}});
    def->connect("self.in", "lb33_inst.in");
    def->connect("self.out", "lb33_inst.out");
  lb33->setDef(def);
  lb33->print();

  bool err = false;
  cout << "Checking saving and loading pregen" << endl;
  saveModule(lb33, "_lb33.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  loadModule(c,"_lb33.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  
  cout << "Running Generators" << endl;
  rungenerators(c,lb33,&err);
  if (err) c->die();
  lb33->print();
  Instance* i = cast<Instance>(lb33->getDef()->sel("lb33_inst"));
  i->getModuleRef()->print();

  cout << "Flattening everything" << endl;
  flatten(c,lb33,&err);
  lb33->print();
  lb33->getDef()->validate();
  
  cout << "Checking saving and loading postgen" << endl;
  saveModule(lb33, "_lb33Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  Module* m = loadModule(c,"_lb33Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();


  deleteContext(c);
}
