#include <fstream>
#include "coreir.h"
#include "coreir/passes/analysis/verilog.h"

using namespace std;
using namespace CoreIR;

int main() {

  // New context
  Context* c = newContext();

  c->getLibraryManager()->loadLib("float");
  c->getLibraryManager()->loadLib("float_CW");
  auto app = c->getGlobal()->newModuleDecl("app", c->Record({}));
  auto def = app->newModuleDef();

  Values bfloatArgs = {{"exp_bits", Const::make(c, 8)},
                       {"frac_bits", Const::make(c, 7)}};
  auto add = def->addInstance("add", "float.add", bfloatArgs);
  auto mul = def->addInstance("mul", "float.mul", bfloatArgs);
  def->connect(add->sel("out"), mul->sel("in0"));
  def->connect(add->sel("out"), mul->sel("in1"));
  def->connect(mul->sel("out"), add->sel("in0"));
  def->connect(mul->sel("out"), add->sel("in1"));
  app->setDef(def);
  app->print();
  c->setTop(app);
  c->runPasses({"rungenerators"});
  // Write to verilog file
  saveToFile(c->getGlobal(), "_float_CW.json");
  deleteContext(c);
}
