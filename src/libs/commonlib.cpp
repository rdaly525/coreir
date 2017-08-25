#include "coreir-lib/commonlib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

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

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {
  
  Namespace* commonlib = c->newNamespace("commonlib");
  Namespace* coreirprims = c->getNamespace("coreir");
 
  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////
  
  Params widthparams = Params({{"width",AINT}});
  // TypeGens defined in coreirprims

  //muxN type
  commonlib->newTypeGen(
    "muxN_type", //name for the typegen
    {{"width",AINT},{"N",AINT}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint width = args.at("width")->get<ArgInt>();
      uint N = args.at("N")->get<ArgInt>();
      return c->Record({
        {"in",c->Record({
              {"data",c->BitIn()->Arr(width)->Arr(N)},
              {"sel",c->BitIn()->Arr(width)}
            })},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  //opN type
  commonlib->newTypeGen(
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


  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
    {"binary",{
     "umin","smin","umax","smax"
    }},
  });
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      commonlib->newGeneratorDecl(op,tg,widthparams);
    }
  }

  /////////////////////////////////
  // definition of not equal     //
  /////////////////////////////////
  Generator* notEqual = commonlib->newGeneratorDecl("neq",coreirprims->getTypeGen("binaryReduce"),{{"width",AINT}});

  notEqual->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();

    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* equal = coreirprims->getGenerator("eq");
    Generator* logicalNot = coreirprims->getGenerator("not");
    
    // create necessary hardware
    Arg* aWidth = c->argInt(width);
    def->addInstance("equal",equal,{{"width",aWidth}});
    def->addInstance("not",logicalNot,{{"width",c->argInt(1)}});

    // connect hardware
    def->connect("self.in0","equal.in0");
    def->connect("self.in1","equal.in1");
    def->connect("equal.out","not.in");
    def->connect("not.out","self.out");

  });

  /////////////////////////////////
  // muxN definition             //
  /////////////////////////////////

  Generator* muxN = commonlib->newGeneratorDecl("muxn",commonlib->getTypeGen("muxN_type"),{{"width",AINT},{"N",AINT}});
  
  muxN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    assert(N>0);

    Namespace* stdlib = c->getNamespace("coreir");
    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* mux2 = stdlib->getGenerator("mux");
    Generator* passthrough = stdlib->getGenerator("passthrough");
    Generator* muxN = commonlib->getGenerator("muxn");
    
    Arg* aWidth = c->argInt(width);
    
    if (N == 1) {
      def->addInstance("passthrough",passthrough,{{"type",c->argType(c->BitIn()->Arr(width))}});
    }
    else if (N == 2) {
      def->addInstance("join",mux2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      def->connect("self.in.data.0","join.in0");
      def->connect("self.in.data.1","join.in1");
      def->connect("self.in.sel.0", "join.sel");
    }
    else {
      def->addInstance("join",mux2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;
      def->connect({"self","in","sel",to_string(Nbits-1)},{"join","sel"});

      cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Arg* aNlarge = c->argInt(Nlargehalf);
      Arg* aNsmall = c->argInt(Nsmallhalf);

      def->addInstance("muxN_0",muxN,{{"width",aWidth},{"N",aNlarge}});
      def->addInstance("muxN_1",muxN,{{"width",aWidth},{"N",aNsmall}});
      for (uint i=0; i<Nlargehalf; ++i) {
        def->connect({"self","in","data",to_string(i)},{"muxN_0","in","data",to_string(i)});
      }
      for (uint i=0; i<Nsmallhalf; ++i) {
        def->connect({"self","in","data",to_string(i+Nlargehalf)},{"muxN_1","in","data",to_string(i)});
      }
      def->connect("muxN_0.out","join.in0");
      def->connect("muxN_1.out","join.in1");
    }

  });

  /////////////////////////////////
  // opN definition             //
  /////////////////////////////////

  Generator* opN = commonlib->newGeneratorDecl("opn",commonlib->getTypeGen("opN_type"),{{"width",AINT},{"N",AINT},{"operator",ASTRING}});
  
  opN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    std::string op2 = args.at("operator")->get<ArgString>();
    assert(N>0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("opn");
    
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


  return commonlib;
}
