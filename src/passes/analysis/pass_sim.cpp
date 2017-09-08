#include "coreir.h"

#include "coreir-passes/analysis/pass_sim.h"
#include "../../simulator/sim.hpp"
#include "../../simulator/output.hpp"

//This is For a convenient macro to create the registerPass and deletePass functions
#include "coreir-macros.h"

using namespace CoreIR;

//Do not forget to set this static variable!!
string SimModule::ID = "simpass";
bool SimModule::runOnModule(Module* m) {

  cout << "RUNNING!!!" << endl;

  NGraph g;
  buildOrderedGraph(m, g);

  auto topoOrder = topologicalSort(g);

  string n = "sim_" + m->getName();

  writeFiles(topoOrder, g, m, n + ".cpp", n + ".h");
  
  return false;
}

void SimModule::print() {
  cout << "SIMULATION CODE!!!" << endl;
}

//This is the macro that will define the registerPass and deletePass functions for you.
COREIR_GEN_EXTERNAL_PASS(SimModule);
