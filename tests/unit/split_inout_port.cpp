#include "coreir.h"

using namespace CoreIR;
using namespace std;

void tribuf_test() {
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

  // en = 1 means data flows into the IO
  // en = 0 means data flows from the IO to the outputs
  sim.setValue("self.en", BitVector(1, 0));
  sim.setValue("self.io_input", BitVector(1, 1));
  sim.setValue("self.to_io", BitVector(1, 0));

  sim.execute();

  assert(sim.getBitVec("self.from_io") == BitVector(1, 1));

  sim.setValue("self.io_input", BitVector(1, 0));

  sim.execute();

  assert(sim.getBitVec("self.from_io") == BitVector(1, 0));

  // Now pass data to the IO
  sim.setValue("self.en", BitVector(1, 1));
  sim.setValue("self.to_io", BitVector(1, 0));

  sim.execute();

  assert(sim.getBitVec("self.from_io") == BitVector(1, 0));
  assert(sim.getBitVec("self.io_output") == BitVector(1, 0));
  
  deleteContext(c);
}

void io_to_io_test() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  uint width = 1;

  {
    Type* tp = c->Record({{"io", c->BitInOut()},
          {"en", c->BitIn()},
            {"from_io", c->Bit()},
              {"to_io", c->BitIn()}});

    Module* inner = g->newModuleDecl("inner", tp);
    ModuleDef* def = inner->newModuleDef();

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

    inner->setDef(def);
  }

  {
    Type* outer_tp =
      c->Record({{"io_port", c->BitInOut()},
            {"in", c->BitIn()},
              {"out", c->Bit()},
                {"en", c->BitIn()}});

    Module* outer = g->newModuleDecl("outer", outer_tp);
    ModuleDef* def = outer->newModuleDef();
    def->addInstance("inner_mod", "global.inner");

    def->connect("self.io_port", "inner_mod.io");
    def->connect("self.en", "inner_mod.en");
    def->connect("self.out", "inner_mod.from_io");
    def->connect("self.in", "inner_mod.to_io");

    outer->setDef(def);

    cout << "PRINT OUTER" << endl;
    outer->print();
  }

  c->runPasses({"rungenerators"});

  cout << "AFTER RUNGENERATORS" << endl;
  auto outer = g->getModule("outer");
  outer->print();

  c->runPasses({"split-inouts", "flatten"});

  cout << "After splitting" << endl;
  outer->print();

  // Note input and output need to be renamed
  SimulatorState sim(outer);

  // when en = 0 data flows from IO input to mod output
  // when en = 1 data flows from input to IO output

  sim.setValue("self.en", BitVector(1, 0));
  sim.setValue("self.in", BitVector(1, 1));
  sim.setValue("self.io_port_input", BitVector(1, 0));

  sim.execute();
  
  assert(sim.getBitVec("self.out") == BitVector(1, 0));

  sim.setValue("self.io_port_input", BitVector(1, 1));

  sim.execute();
  
  assert(sim.getBitVec("self.out") == BitVector(1, 1));

  // Now data flows from input port to IO output
  sim.setValue("self.en", BitVector(1, 1));
  sim.setValue("self.in", BitVector(1, 1));

  sim.execute();

  assert(sim.getBitVec("self.io_port_output") == BitVector(1, 1));

  sim.setValue("self.in", BitVector(1, 0));

  sim.execute();

  assert(sim.getBitVec("self.io_port_output") == BitVector(1, 0));

  deleteContext(c);
}

int main() {
  tribuf_test();
  io_to_io_test();
}
