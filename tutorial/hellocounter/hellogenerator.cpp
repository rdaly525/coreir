#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {

  Context* c = newContext();
  Namespace* global = c->getGlobal();

  Params counterParams({
      {"width",c->Int()},
      {"has_en",c->Bool()}
  });

  TypeGen* counterTypeGen = global->newTypeGen(
    "CounterTypeGen",
    counterParams, 
    [](Context* c, Values genargs) {
      Value* widthArg = genargs.at("width");
      uint width = widthArg->get<int>();
      bool has_en = genargs.at("has_en")->get<bool>();
      RecordParams counterIO = {
        {"out",c->Array(width,c->Bit())},
        {"clk",c->Named("coreir.clkIn")},
      };
      if (has_en) {
        counterIO.push_back({"en",c->BitIn()});
      }
      return c->Record(counterIO);
    }
  );

  Generator* counter = global->newGeneratorDecl("counter",counterTypeGen,counterParams);
  
  Module* top = global->newModuleDecl("counterTestBench",c->Record({{"clk",c->Named("coreir.clkIn")}}));
  ModuleDef* topdef = top->newModuleDef();
    topdef->addInstance("count0","global.counter",{{"width",Const::make(c,32)}, {"has_en",Const::make(c,false)}});
    topdef->addInstance("count1","global.counter",{{"width",Const::make(c,12)}, {"has_en",Const::make(c,true)}});

    topdef->connect("count0.out.31","count1.en");
    topdef->connect("self.clk","count0.clk");
    topdef->connect("self.clk","count1.clk");
  top->setDef(topdef);

  top->print();
  c->runPasses({"verifyconnectivity-onlyinputs"});

  counter->setGeneratorDefFromFun([](Context* c, Values genargs,ModuleDef* def) {
    
    uint width = genargs.at("width")->get<int>();
    bool has_en = genargs.at("has_en")->get<bool>();
     
    Values wArg({{"width",Const::make(c,width)}});
    def->addInstance("ai","coreir.add",wArg);
    def->addInstance("ci","coreir.const",wArg,{{"value",Const::make(c,width,1)}});
    def->addInstance("ri","mantle.reg",{{"width",Const::make(c,width)},{"has_en",Const::make(c,has_en)}});
    
    if (has_en) {
      def->connect("self.en","ri.en");
    }
    def->connect("self.clk","ri.clk");
    def->connect("ci.out","ai.in0");
    def->connect("ai.out","ri.in");
    def->connect("ri.out","ai.in1");
    def->connect("ri.out","self.out");
  });
  
  c->runPasses({"rungenerators","verifyconnectivity-onlyinputs"});

  saveToFile(global,"_counters.json",top);

  //Always remember to delete your context!
  deleteContext(c);
  return 0;
}
