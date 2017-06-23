#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.h"
#include "coreir-pass/common.h"

using namespace CoreIR;

int main() {
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  Namespace* prj = c->newNamespace("prj");
  
  Namespace* sl = CoreIRLoadLibrary_stdlib(c);

  Args wargs({{"width",c->argInt(19)}});
  
  // Define random module with subs
  Module* ms = prj->newModuleDecl("SNRTestSub",c->Any());
  ModuleDef* def = ms->newModuleDef();
    def->addInstance("c0",sl->getGenerator("const"),wargs,{{"value",c->argInt(5)}});
    def->addInstance("c1",sl->getGenerator("const"),wargs,{{"value",c->argInt(5)}});
    def->addInstance("s0",sl->getGenerator("sub"),wargs);
    def->addInstance("s1",sl->getGenerator("sub"),wargs);
    def->addInstance("m0",sl->getGenerator("mul"),wargs);
    def->connect("c0.out","s0.in.0");
    def->connect("c1.out","s0.in.1");
    def->connect("s0.out","s1.in.0");
    def->connect("s0.out","s1.in.1");
    def->connect("s1.out","m0.in.0");
    def->connect("s0.out","m0.in.1");
  ms->setDef(def);
  ms->print();
  
  // Define same random module with adds instead of subs
  Module* ma = g->newModuleDecl("SNRTestAdd",c->Any());
  def = ma->newModuleDef();
    def->addInstance("c0",sl->getGenerator("const"),wargs,{{"value",c->argInt(5)}});
    def->addInstance("c1",sl->getGenerator("const"),wargs,{{"value",c->argInt(5)}});
    def->addInstance("a0",sl->getGenerator("add"),wargs);
    def->addInstance("a1",sl->getGenerator("add"),wargs);
    def->addInstance("m0",sl->getGenerator("mul"),wargs);
    def->connect("c0.out","a0.in.0");
    def->connect("c1.out","a0.in.1");
    def->connect("a0.out","a1.in.0");
    def->connect("a0.out","a1.in.1");
    def->connect("a1.out","m0.in.0");
    def->connect("a0.out","m0.in.1");
  ma->setDef(def);
  ma->print();

  //Now try to do a search and replace on ms to replace all subs with adds
  
  PassManager* pm = new PassManager(prj);

  //Create all the search and replace patterns. 
  Namespace* patns = c->newNamespace("mapperpatterns");

  //Create the match pattern and the replace pattern for Sub2Add
  Type* subType = sl->getTypeGen("binary")->getType(wargs);
  Module* patternSub = patns->newModuleDecl("sub",subType);
  ModuleDef* pdef = patternSub->newModuleDef();
    pdef->addInstance("inst",sl->getGenerator("sub"),wargs);
    pdef->connect("self","inst");
  patternSub->setDef(pdef);

  MatchAndReplacePass* pSub2Add = new MatchAndReplacePass(
      patternSub,
      sl->getGenerator("add")->getModule(wargs)
  );
  pm->addPass(pSub2Add,0);
  
  cout << "Running all the passes!" << endl;
  pm->run();
  cout << "Printing the (hompefully) modified graph" << endl;
  ms->print();

  deleteContext(c);
  
  return 0;
}
