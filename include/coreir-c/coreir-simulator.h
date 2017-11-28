#ifndef COREIR_SIMULATOR_H
#define COREIR_SIMULATOR_H

#include <coreir-c/ctypes.h>

extern bool CORESimValueGetBit(CORESimValue *val, int bit);
extern int CORESimValueGetLength(CORESimValue *val);
extern CORESimulatorState *CORENewSimulatorState(COREModule* module);
extern void COREDeleteSimulatorState(CORESimulatorState* state);
extern CORESimValue* CORESimGetValue(CORESimulatorState* cstate, char** cpath, int path_len);
extern CORESimValue* CORESimGetValueByOriginalName(CORESimulatorState* cstate, char** inst_path, int inst_path_len, char** port_selects, int port_selects_len);
extern void CORESimSetMainClock(CORESimulatorState* cstate, char** cpath, int path_leN);
extern void CORESimSetClock(CORESimulatorState* cstate, char** cpath, int path_len, bool lastval, bool curval);
extern int CORESimGetClockCycles(CORESimulatorState* cstate, char** cpath, int path_len);
extern void CORESimSetValue(CORESimulatorState* cstate, char** cpath, int path_len, bool* new_val, int val_len);
extern void CORESimResetCircuit(CORESimulatorState* cstate);
extern void CORESimRunHalfCycle(CORESimulatorState* cstate);
extern void CORESimStepMainClock(CORESimulatorState* cstate);
extern void CORESimRun(CORESimulatorState* cstate);
extern void CORESimExecute(CORESimulatorState* cstate);
extern bool CORESimRewind(CORESimulatorState* cstate, int halfCycles);
extern void CORESimSetWatchPoint(CORESimulatorState* cstate, char** cpath, int path_len, bool* watch_val, int watch_len);

#endif
