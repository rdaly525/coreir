#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"

using namespace CoreIR;

Type* binop_type(Context* c, Args args, Params params) {
  int n = args.at("width")->arg2Int();
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}

Type* addN_type(Context* c, Args args) {
  int width = args.at("width")->arg2Int();
  int n = args.at("n")->arg2Int();
  return c->Record({
    {"in", c->Array(n,c->Array(width,c->BitIn()))},
    {"out", c->Array(width,c->BitOut())}
  });
}

void addN(Context* c, Module* m, Args args, Params params) {
  int width = args.at("width")->arg2Int();
  int n = args.at("N")->arg2Int();
  Args add2Args = {{"width",width}};
  ModuleDef* def = m->newModuleDef();
  if (n == 1) {
    def->wire({"self","in"},{"self","out"});
  }
  else if (n == 2) {
    def->addInstance("inst",add2,add2Args);
    def->wire({"inst","in0"},{"self","in","0"});
    def->wire({"inst","in1"},{"self","in","1"});
    def->wire({"inst","out"},{"self","out"});
  }
  else {
    //Connect half instances
    n_2 = int(n/2);
    def->addInstance("addN_0",addN,{{"width",width},{"N",n_2}});
    def->addInstance("addN_1",addN,{{"width",width},{"N",n_2}});
    for (uint i=0; i<n_2; ++i) {
      def->wire({"self","in",to_string(i)},{"addN_0","in",to_string(i)});
      def->wire({"self","in",to_string(i+n_2)},{"addN_1","in",to_string(i)});
    }
    def->addInstance("inst",add2,add2Args);
    def->wire({"addN_0","out"},{"inst","in0"});
    def->wire({"addN_1","out"},{"inst","in1"});
    if (n%2==0) {
      def->wire({"inst","out"},{"self","out"});
    }
    else {
      def->addInstance("instOdd",add2,add2Args);
      def->wire({"inst","out"},{"instOdd","in0"});
      def->wire({"self","in",to_string(n-1)},{"instOdd","in1"});
      def->wire({"instOdd","out"},{"self","out"});
    }
  }
  m->addDef(def);
}


Module* add2(Context* c, Type* t, Args args, Params params) {
  int width = args.at("width")->arg2Int();
  Module* m = c->getGlobal()->newModuleDecl("add2_"+to_string(width),t);
  string verilog = "Verilog NYI add2";
  //VModule vm(m);
  //vm.addstmt(VAssign("out","in0 + in1"));
  //m->addVerilog(vm.toString());
  m->addVerilog(verilog);
  return m;
}

Namespace* getStdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
  
  //Add bop typegen to library
  stdlib->newTypeGen("binop","binop_F",{{"width",AINT}},binop_type);
  
  //declare new add2 generator
  Generator* g = stdlib->newGeneratorDecl("add2",{{"width",AINT}},stdlib->getTypeGen("binop"));
  g->addDef(add2);
  
  //Type* binop16 = binop_type(c,c->genArgs({{"width",c->int2Arg(16)}}),{{"width",AINT}});
  Type* binop16 = c->Record({
      {"in0",c->Array(16,c->BitIn())},
      {"in1",c->Array(16,c->BitIn())},
      {"out",c->Array(16,c->BitOut())}
  });
  
  Type* outType = c->Record({
    {"out",c->Array(16,c->BitOut())}
  });

  Type* inType = c->Record({
    {"in",c->Array(16,c->BitIn())}
  });

  stdlib->newModuleDecl("add2_16",binop16);
  stdlib->newModuleDecl("mult2_16",binop16);
  stdlib->newModuleDecl("const_16",outType,{{"value",AINT}});
  stdlib->newModuleDecl("GPI_16",outType);
  stdlib->newModuleDecl("GPO_16",inType);
  return stdlib;
}

#endif //STDLIB_HPP_
