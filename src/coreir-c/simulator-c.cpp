#include "coreir-c/coreir-simulator.h"
#include "coreir.h"
#include "common-c.hpp"
#include "../simulator/interpret.hpp"

using namespace std;
namespace CoreIR {

static vector<string> MakeSimPath(char** cpath, int len) {
  vector<string> path;
  for (int i = 0; i < len; i++) {
    path.emplace_back(cpath[i]);
  }

  return path;
}

extern "C" {

  bool CORESimValueGetBit(CORESimValue* cval, int bit) {
    SimValue* val = rcast<SimValue*>(cval);
    if (val->getType() == SIM_VALUE_BV) {
      SimBitVector* bv = static_cast<SimBitVector*>(val);
      return bv->getBits().get(bit);
    }
    else if (val->getType() == SIM_VALUE_CLK) {
      ClockValue* cv = static_cast<ClockValue*>(val);
      return cv->value();
    }
    return false;
  }

  int CORESimValueGetLength(CORESimValue* cval) {
    SimValue* val = rcast<SimValue*>(cval);
    if (val->getType() == SIM_VALUE_BV) {
      SimBitVector* bv = static_cast<SimBitVector*>(val);
      return bv->getBits().bitLength();
    } else if (val->getType() == SIM_VALUE_CLK) {
      return 1;
    }
    return 0;
  }

  CORESimulatorState* CORENewSimulatorState(COREModule* module) {
    Module* top = rcast<Module*>(module);
    SimulatorState* state = new SimulatorState(top);

    return rcast<CORESimulatorState*>(state);
  }

  void COREDeleteSimulatorState(CORESimulatorState* state) {
    delete rcast<SimulatorState*>(state);
  }

  CORESimValue* CORESimGetValue(CORESimulatorState* cstate, char** cpath, int path_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);

    return rcast<CORESimValue*>(state->getValue(path));
  }

  void CORESimSetValue(CORESimulatorState* cstate, char** cpath, int path_len, bool* new_val, int val_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);
    BitVec bv(val_len);
    for (int i = 0; i < val_len; i++) {
      bv.set(i, new_val[i]);
    }
    state->setValue(path, bv);
  }
   
  void CORESimStepMainClock(CORESimulatorState* cstate) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    state->stepMainClock();
  }

  void CORESimRun(CORESimulatorState* cstate) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    state->run();
  }

  void CORESimExecute(CORESimulatorState* cstate) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    state->execute();
  }

  bool CORESimRewind(CORESimulatorState* cstate, int halfCycles) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    return state->rewind(halfCycles);
  }

  void CORESimSetWatchPoint(CORESimulatorState* cstate, char** cpath, int path_len, bool* watch_val, int watch_len) {
    SimulatorState *state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);
    BitVec bv(watch_len);
    for (int i = 0; i < watch_len; i++) {
      bv.set(i, watch_val[i]);
    }
    state->setWatchPoint(path, bv);
  }

}//extern "C"
}//CoreIR namespace
