#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.h"

#include <string>   // std::string
#include <iostream> // std::cout
#include <sstream>  // std::stringstream

using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);
 
  //Type of module 
  Type* addmultType = c->Record({
    {"in",c->Array(16,c->BitIn())},
    {"out",c->Array(16,c->Bit())}
  });
  Args w16({{"width",c->argInt(16)}});
  Generator* Add = stdlib->getGenerator("add");
  Generator* Mul = stdlib->getGenerator("mul");
  Generator* Const = stdlib->getGenerator("const");
  Module* addmult = c->getGlobal()->newModuleDecl("addmult",addmultType);
  ModuleDef* def = addmult->newModuleDef();
  def->addInstance("ai", dynamic_cast<Instantiable*>(Add), w16);  // Test Instantiable* interface
  def->addInstance("mi", Mul, w16);
  def->addInstance("ci", Const, w16,{{"value",c->argInt(140)}});
  
  def->connect("self.in","ai.in.0");
  def->connect("ci.out","ai.in.1");
  def->connect("ci.out","mi.in.0");
  def->connect("ai.out","mi.in.1");
  def->connect("mi.out","self.out");
  addmult->setDef(def);
  std::stringstream buffer;
  std::streambuf* prevcoutbuf = std::cout.rdbuf(buffer.rdbuf());
  addmult->print();
  std::string text = buffer.str();
  int result = text.compare( 
"Module: addmult"
"  Type: {'in':BitIn[16], 'out':Bit[16]}"
"  Def? Yes"
"  Def:"
"    Instances:"
"      ci : const(width:16)"
"      mi : mul(width:16)"
"      ai : add(width:16)"
"    Connections:"
"      ai.out <=> mi.in[1]"
"      ci.out <=> mi.in[0]"
"      mi.out <=> self.out"
"      ci.out <=> ai.in[1]"
"      self.in <=> ai.in[0]");


  // Restore original buffer before exiting
  std::cout.rdbuf(prevcoutbuf);
  if (!result) {
      std::cout << "Failed" << std::endl;
      std::exit(1);
  }
  std::cout << "Success" << std::endl;
  std::exit(0);
}
