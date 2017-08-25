#include "coreir.h"

using namespace CoreIR;

uint num_bits(uint N) {
  uint num_shifts = 0;
  uint temp_value = N;
  while (temp_value > 0) {
    temp_value  = temp_value >> 1;
    num_shifts++;
  }
  return num_shifts;
}

int main() {

  Context* c = newContext();
  Namespace* global = c->getGlobal();
  

  /////////////////////////////////
  // opN definition             //
  /////////////////////////////////

  //opN type
  global->newTypeGen(
    "opN_type", //name for the typegen
    {{"width",AINT},{"N",AINT},{"operator",ASTRING}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint width = args.at("width")->get<ArgInt>();
      uint N = args.at("N")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(N)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  Generator* opN = global->newGeneratorDecl("treen",global->getTypeGen("opN_type"),{{"width",AINT},{"N",AINT},{"operator",ASTRING}});
  
  opN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    std::string op2 = args.at("operator")->get<ArgString>();
    assert(N>0);

    Generator* opN = c->getGlobal()->getGenerator("treen");
    
    Arg* aWidth = c->argInt(width);
    Arg* aOperator = c->argString(op2);
    
    if (N == 1) {
      def->addInstance("passthrough","coreir.passthrough",{{"type",c->argType(c->BitIn()->Arr(width))}});
    }
    else if (N == 2) {
      def->addInstance("join",op2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      def->connect("self.in.0","join.in0");
      def->connect("self.in.1","join.in1");
    }
    else {
      def->addInstance("join",op2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;

      cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Arg* aNlarge = c->argInt(Nlargehalf);
      Arg* aNsmall = c->argInt(Nsmallhalf);

      def->addInstance("opN_0",opN,{{"width",aWidth},{"N",aNlarge},{"operator",aOperator}});
      def->addInstance("opN_1",opN,{{"width",aWidth},{"N",aNsmall},{"operator",aOperator}});
      for (uint i=0; i<Nlargehalf; ++i) {
        def->connect({"self","in",to_string(i)},{"opN_0","in",to_string(i)});
      }
      for (uint i=0; i<Nsmallhalf; ++i) {
        def->connect({"self","in",to_string(i+Nlargehalf)},{"opN_1","in",to_string(i)});
      }
      def->connect("opN_0.out","join.in0");
      def->connect("opN_1.out","join.in1");
    }

  });

  // TEST //
  //Module* tb = global->newModuleDecl("treeTestBench",c->Record({})); //empty record means no ports
  Type* add15Type = c->Record({
        {"in",c->BitIn()->Arr(16)->Arr(15)},
        {"out",c->Bit()->Arr(16)}
      });

  Module* add15 = c->getGlobal()->newModuleDecl("add15", add15Type);
  ModuleDef* def = add15->newModuleDef();
    def->addInstance("add15", "global.treen", 
                     {{"width",c->argInt(16)},{"N",c->argInt(15)},{"operator",c->argString("coreir.add")}}
                     );
    def->connect("self.in", "add15.in");
    def->connect("self.out", "add15.out");
  
  add15->setDef(def);
  //add15->print();
  c->runPasses({"rungenerators","flatten"});
  add15->print();
  saveToDot(add15, "design.txt");

}
