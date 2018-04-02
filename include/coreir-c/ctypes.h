#ifndef COREIR_CTYPES_H_
#define COREIR_CTYPES_H_

#include <stdint.h>
#include <stdbool.h>

typedef struct COREContext COREContext;
typedef struct CORENamespace CORENamespace;
typedef struct COREGlobalValue COREGlobalValue;
typedef struct COREType COREType;
typedef struct COREModule COREModule;
typedef struct COREGenerator COREGenerator;
typedef struct COREModuleDef COREModuleDef;
typedef struct COREWireable COREWireable;
typedef struct COREConnection COREConnection;
typedef struct COREWirePath COREWirePath;
typedef struct COREValue COREValue;
typedef struct COREValueType COREValueType;

typedef struct COREDirectedConnection COREDirectedConnection;
typedef struct COREDirectedModule COREDirectedModule;
typedef struct COREDirectedInstance COREDirectedInstance;

typedef struct CORESimulatorState CORESimulatorState;
typedef struct CORESimValue CORESimValue;

typedef enum {
  STR2TYPE_ORDEREDMAP = 0,
  STR2VALUETYPE_MAP = 1,
  STR2VALUE_MAP = 2
} COREMapKind;


#endif //COREIR_CTYPES_H_
