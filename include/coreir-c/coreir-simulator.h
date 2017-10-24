#ifndef COREIR_SIMULATOR_H
#define COREIR_SIMULATOR_H

#include <coreir-c/ctypes.h>

extern bool CORESimValueGetBit(CORESimValue *val, int bit);
extern int CORESimValueGetLength(CORESimValue *val);
extern CORESimulatorState *CORENewSimulatorState(COREModule* module);
extern void COREDeleteSimulatorState(CORESimulatorState* state);
extern CORESimValue* CORESimGetValue(CORESimulatorState* cstate, char** cpath, int path_len);
extern void CORESimSetValue(CORESimulatorState* cstate, char** cpath, int path_len, bool* new_val);
extern void CORESimStepMainClock(CORESimulatorState* cstate);
extern void CORESimRun(CORESimulatorState* cstate);
extern void CORESimExecute(CORESimulatorState* cstate);
extern bool CORESimRewind(CORESimulatorState* cstate, int halfCycles);
extern void CORESimSetWatchPoint(CORESimulatorState* cstate, char** cpath, int path_len, bool* watch_val);

#endif
