#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  uint width = 1;
  
  Type* tp = c->Record({{"io", c->BitInOut()},
        {"en", c->BitIn()},
          {"from_io", c->Bit()},
            {"to_io", c->BitIn()}});

  Module* io = g->newModuleDecl("io", tp);
  ModuleDef* def = io->newModuleDef();

  def->addInstance("tristate_buf",
                   "coreir.tribuf",
                   {{"width", Const::make(c, width)}});

  def->addInstance("tristate_out",
                   "coreir.ibuf",
                   {{"width", Const::make(c, width)}});

  def->connect("tristate_buf.en", "self.en");
  def->connect("tristate_buf.in.0", "self.to_io");
  def->connect("tristate_buf.out.0", "self.io");

  def->connect("tristate_out.in.0", "self.io");
  def->connect("tristate_out.out.0", "self.from_io");

  io->setDef(def);

  cout << "Before splitting" << endl;
  io->print();

  c->runPasses({"split-inouts"});

  cout << "After splitting" << endl;
  io->print();

  assert(def->getInstances().size() == 1);

  SimulatorState sim(io);

  sim.setValue("self.en", BitVector(1, 0));
  sim.setValue("self.io_output", BitVector(1, 1));
  sim.setValue("self.to_io", BitVector(1, 0));

  sim.execute();

  assert(sim.getBitVec("self.from_io") == BitVector(1, 1));

  sim.setValue("self.en", BitVector(1, 1));

  sim.execute();

  assert(sim.getBitVec("self.from_io") == BitVector(1, 0));
  assert(sim.getBitVec("self.io_input") == BitVector(1, 0));
  
  deleteContext(c);
}
