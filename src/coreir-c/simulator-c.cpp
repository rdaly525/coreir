#include "coreir-c/coreir-simulator.h"
#include "coreir.h"
#include "common-c.hpp"
#include "coreir/simulator/interpreter.h"

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
      return bv->getBits().get(bit).binary_value();
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

  CORESimValue* CORESimGetValueByOriginalName(CORESimulatorState* cstate, char** inst_path, int inst_path_len, char** port_selects, int port_selects_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> instPath = MakeSimPath(inst_path,inst_path_len);
    vector<string> selects = MakeSimPath(port_selects,port_selects_len);
    //TODO uncomment
    return rcast<CORESimValue*>(state->getValueByOriginalName(instPath,selects));
    return nullptr;
  }

  void CORESimResetCircuit(CORESimulatorState* cstate) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    state->resetCircuit();
  }
  
  void CORESimSetMainClock(CORESimulatorState* cstate, char** cpath, int path_len) {
    SimulatorState*state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);
    state->setMainClock(path);
  }

  void CORESimSetClock(CORESimulatorState* cstate, char** cpath, int path_len, bool lastval, bool curval) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);

    state->setClock(path, lastval, curval);
  }

  int CORESimGetClockCycles(CORESimulatorState* cstate, char** cpath, int path_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> path = MakeSimPath(cpath, path_len);
    ClockValue* clk = toClock(state->getValue(path));
    return clk->getCycleCount();
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

  void CORESimRunHalfCycle(CORESimulatorState* cstate) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    state->runHalfCycle();
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

  void CORESimDeleteWatchPointByOriginalName(CORESimulatorState* cstate, char** inst_path, int inst_path_len, char** port_selects, int port_selects_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> instPath = MakeSimPath(inst_path, inst_path_len);
    vector<string> selects = MakeSimPath(port_selects, port_selects_len);
    state->deleteWatchPointByOriginalName(instPath, selects);
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

  void CORESimSetWatchPointByOriginalName(CORESimulatorState* cstate, char** inst_path, int inst_path_len, char** port_selects, int port_selects_len, bool *watch_val, int watch_len) {
    SimulatorState* state = rcast<SimulatorState*>(cstate);
    vector<string> instPath = MakeSimPath(inst_path, inst_path_len);
    vector<string> selects = MakeSimPath(port_selects, port_selects_len);
    BitVec bv(watch_len);
    for (int i = 0; i < watch_len; i++) {
      bv.set(i, watch_val[i]);
    }

    state->setWatchPointByOriginalName(instPath, selects, bv);
  }

  void COREEnSymtable(COREContext* core_ctx) {
    Context *ctx = rcast<Context*>(core_ctx);
    ctx->enSymtable();
  }


}//extern "C"
}//CoreIR namespace
