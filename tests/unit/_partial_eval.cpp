#include "coreir.h"

#include <string>
#include <fstream>
#include <streambuf>

#include "coreir/libs/rtlil.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"
#include "coreir/passes/transform/packconnections.h"

using namespace CoreIR;
using namespace std;

int main() {

  cout << "Starting partial eval test" << endl;

  Context* c = newContext();

  Module* topMod = loadModule(c, "circuits/registered_switch_proc_flat_sanitized_names.json", "registered_switch");
  auto def = topMod->getDef();

  BitVector configData(32, 0x00000C00);
  
  SimulatorState originalState(topMod);
  originalState.setClock("self.clk", 0, 1);
  originalState.setValue("self.config_en", BitVec(1, 1));
  originalState.setValue("self.config_addr", BitVec(32, 0));
  originalState.setValue("self.config_data", configData);

  originalState.setValue("self.in_0_0", BitVec(16, 0));
  originalState.setValue("self.in_2_0", BitVec(16, 0));
  originalState.setValue("self.in_3_0", BitVec(16, 0));
  originalState.setValue("self.pe_output_0", BitVec(16, 0));
  
  originalState.execute();

  originalState.setValue("self.config_en", BitVec(1, 0));

  originalState.setValue("self.in_0_0", BitVec(16, 1));
  originalState.setValue("self.in_2_0", BitVec(16, 2));
  originalState.setValue("self.in_3_0", BitVec(16, 3));
  originalState.setValue("self.pe_output_0", BitVec(16, 34));
    
  originalState.setValue("self.config_en", BitVec(1, 0));
  originalState.setValue("self.pe_output_0", BitVec(16, 34));

  originalState.execute();

  cout << "original self.out_1_0 = " << originalState.getBitVec("self.out_1_0") << endl;
  
  assert(originalState.getBitVec("self.out_1_0") == BitVec(16, 34));
  
  // Insert partial eval code
  vector<Wireable*> subCircuitPorts{def->sel("self")->sel("config_addr"),
      def->sel("self")->sel("config_data"),
      def->sel("self")->sel("clk"),
      def->sel("self")->sel("config_en")};
  
  auto subCircuitInstances =
    extractSubcircuit(topMod, subCircuitPorts);

  cout << "# of instances in subciruit = " << subCircuitInstances.size() << endl;

  Module* topMod_conf =
    createSubCircuit(topMod,
                     subCircuitPorts,
                     subCircuitInstances,
                     c);
  
  SimulatorState topState(topMod_conf);
  topState.setClock("self.clk", 0, 1);
  topState.setValue("self.config_en", BitVec(1, 1));
    
  topState.setValue("self.config_addr", BitVec(32, 0));
  topState.setValue("self.config_data", configData);

  topState.execute();

  Module* wholeTopMod = nullptr;
  wholeTopMod = c->getGlobal()->getModule("registered_switch");
  assert(wholeTopMod != nullptr);
  c->setTop(wholeTopMod);

  auto regMap = topState.getCircStates().back().registers;
  cout << "Partially evaluating the switch box" << endl;

  cout << "# of instances in circuit before partial evaluation = " << wholeTopMod->getDef()->getInstances().size() << endl;

  partiallyEvaluateCircuit(wholeTopMod, regMap);

  cout << "# of instances in circuit after partial evaluation  = " << wholeTopMod->getDef()->getInstances().size() << endl;
  cout << "Module" << endl;
  wholeTopMod->print();

  cout << "Saving the partially evaluated circuit" << endl;
  if (!saveToFile(c->getGlobal(),
                  "registered_switch_partially_evaluated.json",
                  wholeTopMod)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  SimulatorState state(wholeTopMod);

  state.setClock("self.clk", 0, 1);
  state.setValue("self.config_en", BitVec(1, 0));

  state.setValue("self.in_0_0", BitVec(16, 1));
  state.setValue("self.in_2_0", BitVec(16, 2));
  state.setValue("self.in_3_0", BitVec(16, 3));
  state.setValue("self.pe_output_0", BitVec(16, 34));
    
  state.setValue("self.config_en", BitVec(1, 0));
  state.setValue("self.pe_output_0", BitVec(16, 34));

  state.execute();

  cout << "self.out_1_0 = " << state.getBitVec("self.out_1_0") << endl;
  
  assert(state.getBitVec("self.out_1_0") == BitVec(16, 34));

  state.setValue("self.pe_output_0", BitVec(16, 2));

  state.execute();

  cout << "self.out_1_0 = " << state.getBitVec("self.out_1_0") << endl;

  assert(state.getBitVec("self.out_1_0") == BitVec(16, 2));

  deleteContext(c);

  return 0;
}
