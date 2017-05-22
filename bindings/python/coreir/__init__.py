from ctypes import cdll
import ctypes as ct
import platform
import os
from coreir.lib import load_shared_lib, libcoreir_c
from coreir.context import COREContext, COREContext_p, Context, COREMapKind, COREMapKind_STR2ARG_MAP, COREMapKind_STR2PARAM_MAP, COREMapKind_STR2ARG_MAP
from coreir.module import COREModule, COREModule_p, COREModuleDef, COREModuleDef_p, ModuleDef, Module, \
        COREDirectedInstance_p, COREDirectedConnection_p, COREDirectedModule_p
from coreir.namespace import CORENamespace, CORENamespace_p
from coreir.type import COREType, COREType_p, CoreIRType, Params, Args, COREArg, COREArg_p, Type
from coreir.wireable import COREInstance_p, COREWireable_p, CORESelect_p, COREInterface_p
from collections import namedtuple

class COREConnection(ct.Structure):
    pass

COREConnection_p = ct.POINTER(COREConnection)

libcoreir_c.CORENewMap.argtypes = [COREContext_p, ct.c_void_p, ct.c_void_p, ct.c_uint32, COREMapKind]
libcoreir_c.CORENewMap.restype = ct.c_void_p

libcoreir_c.CORENewContext.restype = COREContext_p

libcoreir_c.COREPrintErrors.argtypes = [COREContext_p]

libcoreir_c.COREAny.argtypes = [COREContext_p]
libcoreir_c.COREAny.restype = COREType_p

libcoreir_c.COREBitIn.argtypes = [COREContext_p]
libcoreir_c.COREBitIn.restype = COREType_p

libcoreir_c.COREBit.argtypes = [COREContext_p]
libcoreir_c.COREBit.restype = COREType_p

libcoreir_c.COREArray.argtypes = [COREContext_p, ct.c_uint32, COREType_p]
libcoreir_c.COREArray.restype = COREType_p

libcoreir_c.CORERecord.argtypes = [COREContext_p, ct.c_void_p]
libcoreir_c.CORERecord.restype = COREType_p

libcoreir_c.COREPrintType.argtypes = [COREType_p, ]

libcoreir_c.CORELoadModule.argtypes = [COREContext_p, ct.c_char_p, ct.POINTER(ct.c_bool)]
libcoreir_c.CORELoadModule.restype = COREModule_p

libcoreir_c.CORESaveModule.argtypes = [COREModule_p, ct.c_char_p, ct.POINTER(ct.c_bool)]

libcoreir_c.COREGetGlobal.argtypes = [COREContext_p]
libcoreir_c.COREGetGlobal.restype = CORENamespace_p

libcoreir_c.CORENewModule.argtypes = [CORENamespace_p, ct.c_char_p, COREType_p, ct.c_void_p]
libcoreir_c.CORENewModule.restype = COREModule_p

libcoreir_c.COREModuleSetDef.argtypes = [COREModule_p, COREModuleDef_p]

libcoreir_c.COREPrintModule.argtypes = [COREModule_p]

libcoreir_c.COREModuleNewDef.argtypes = [COREModule_p]
libcoreir_c.COREModuleNewDef.restype = COREModuleDef_p

libcoreir_c.COREModuleGetDef.argtypes = [COREModule_p]
libcoreir_c.COREModuleGetDef.restype = COREModuleDef_p

libcoreir_c.COREModuleDefAddModuleInstance.argtypes = [COREModuleDef_p, ct.c_char_p, COREModule_p, ct.c_void_p]
libcoreir_c.COREModuleDefAddModuleInstance.restype = COREInstance_p

libcoreir_c.COREModuleDefGetInterface.argtypes = [COREModuleDef_p]
libcoreir_c.COREModuleDefGetInterface.restype = COREInterface_p

libcoreir_c.COREModuleDefGetInstances.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREModuleDefGetInstances.restype = ct.POINTER(COREInstance_p)

libcoreir_c.COREModuleGetDirectedModule.argtypes = [COREModule_p]
libcoreir_c.COREModuleGetDirectedModule.restype = COREDirectedModule_p

libcoreir_c.COREGetInstRefName.argtypes = [COREInstance_p]
libcoreir_c.COREGetInstRefName.restype = ct.c_char_p

libcoreir_c.COREGetConfigValue.argtypes = [COREInstance_p,ct.c_char_p]
libcoreir_c.COREGetConfigValue.restype = COREArg_p;

libcoreir_c.COREArg2Str.argtypes = [COREArg_p]
libcoreir_c.COREArg2Str.restype = ct.c_char_p

libcoreir_c.COREArg2Int.argtypes = [COREArg_p]
libcoreir_c.COREArg2Int.restype = ct.c_int

libcoreir_c.COREInt2Arg.argtypes = [COREContext_p,ct.c_int]
libcoreir_c.COREInt2Arg.restype = COREArg_p

libcoreir_c.COREStr2Arg.argtypes = [COREContext_p,ct.c_char_p]
libcoreir_c.COREStr2Arg.restype = COREArg_p

libcoreir_c.COREModuleDefGetConnections.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREModuleDefGetConnections.restype = ct.POINTER(COREConnection_p)

libcoreir_c.COREConnectionGetFirst.argtypes = [COREConnection_p]
libcoreir_c.COREConnectionGetFirst.restype = COREWireable_p

libcoreir_c.COREConnectionGetSecond.argtypes = [COREConnection_p]
libcoreir_c.COREConnectionGetSecond.restype = COREWireable_p

libcoreir_c.COREModuleDefConnect.argtypes = [COREModuleDef_p, COREWireable_p, COREWireable_p]

libcoreir_c.COREInterfaceSelect.argtypes = [COREInterface_p, ct.c_char_p]
libcoreir_c.COREInterfaceSelect.restype = CORESelect_p

libcoreir_c.COREInstanceSelect.argtypes = [COREInstance_p, ct.c_char_p]
libcoreir_c.COREInstanceSelect.restype = CORESelect_p

libcoreir_c.COREPrintModuleDef.argtypes = [COREModuleDef_p]

libcoreir_c.COREWireableGetConnectedWireables.argtypes = [COREWireable_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREWireableGetConnectedWireables.restype = ct.POINTER(COREWireable_p)

libcoreir_c.COREWireableGetModuleDef.argtypes = [COREWireable_p]
libcoreir_c.COREWireableGetModuleDef.restype = COREModuleDef_p

libcoreir_c.COREWireableSelect.argtypes = [COREWireable_p, ct.c_char_p]
libcoreir_c.COREWireableSelect.restype = CORESelect_p

libcoreir_c.COREWireableGetSelectPath.argtypes = [COREWireable_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREWireableGetSelectPath.restype = ct.POINTER(ct.c_char_p)

libcoreir_c.COREModuleDefSelect.argtypes = [COREModuleDef_p, ct.c_char_p]
libcoreir_c.COREModuleDefSelect.restype = CORESelect_p

libcoreir_c.COREModuleDefGetModule.argtypes = [COREModuleDef_p]
libcoreir_c.COREModuleDefGetModule.restype = COREModule_p

libcoreir_c.CORENamespaceGetName.argtypes = [CORENamespace_p]
libcoreir_c.CORENamespaceGetName.restype = ct.c_char_p

# libcoreir_c.CORESelectGetParent.argtypes = [CORESelect_p]
# libcoreir_c.CORESelectGetParent.restype = COREWireable_p

libcoreir_c.COREDirectedModuleSel.argtypes = [COREDirectedModule_p, ct.POINTER(ct.c_char_p), ct.c_int]
libcoreir_c.COREDirectedModuleSel.restype = COREWireable_p

libcoreir_c.COREDirectedModuleGetInstances.argtypes = [COREDirectedModule_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedModuleGetInstances.restype = ct.POINTER(COREDirectedInstance_p)

libcoreir_c.COREDirectedModuleGetInputs.argtypes = [COREDirectedModule_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedModuleGetInputs.restype = ct.POINTER(COREDirectedConnection_p)

libcoreir_c.COREDirectedModuleGetOutputs.argtypes = [COREDirectedModule_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedModuleGetOutputs.restype = ct.POINTER(COREDirectedConnection_p)

libcoreir_c.COREDirectedModuleGetConnections.argtypes = [COREDirectedModule_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedModuleGetConnections.restype = ct.POINTER(COREDirectedConnection_p)

libcoreir_c.COREDirectedConnectionGetSrc.argtypes = [COREDirectedConnection_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedConnectionGetSrc.restype = ct.POINTER(ct.c_char_p)

libcoreir_c.COREDirectedConnectionGetSnk.argtypes = [COREDirectedConnection_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedConnectionGetSnk.restype = ct.POINTER(ct.c_char_p)

libcoreir_c.COREDirectedInstanceGetInputs.argtypes = [COREDirectedInstance_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedInstanceGetInputs.restype = ct.POINTER(COREDirectedConnection_p)

libcoreir_c.COREDirectedInstanceGetOutputs.argtypes = [COREDirectedInstance_p, ct.POINTER(ct.c_int)]
libcoreir_c.COREDirectedInstanceGetOutputs.restype = ct.POINTER(COREDirectedConnection_p)
