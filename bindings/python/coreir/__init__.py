from ctypes import cdll
import ctypes as ct
import platform
import os
from coreir.lib import load_shared_lib, libcoreir_c
from collections import namedtuple

class COREContext(ct.Structure):
    pass

COREContext_p = ct.POINTER(COREContext)

class CORENamespace(ct.Structure):
    pass

CORENamespace_p = ct.POINTER(CORENamespace)

class COREType(ct.Structure):
    pass

COREType_p = ct.POINTER(COREType)

class COREModule(ct.Structure):
    pass

COREModule_p = ct.POINTER(COREModule)

class COREModuleDef(ct.Structure):
    pass

COREModuleDef_p = ct.POINTER(COREModuleDef)

class COREArg(ct.Structure):
  pass

COREArg_p = ct.POINTER(COREArg)

class COREInterface(ct.Structure):
    pass

COREInterface_p = ct.POINTER(COREInterface)

class COREWireable(ct.Structure):
    pass

COREWireable_p = ct.POINTER(COREWireable)

class COREInstance(COREWireable):
    pass

COREInstance_p = ct.POINTER(COREInstance)

class CORESelect(COREWireable):
    pass

CORESelect_p = ct.POINTER(CORESelect)

class COREConnection(ct.Structure):
    pass

COREConnection_p = ct.POINTER(COREConnection)

class COREDirectedInstance(ct.Structure):
    pass

COREDirectedInstance_p = ct.POINTER(COREDirectedInstance)

class COREDirectedConnection(ct.Structure):
    pass

COREDirectedConnection_p = ct.POINTER(COREDirectedConnection)

class COREDirectedModule(ct.Structure):
    pass

COREDirectedModule_p = ct.POINTER(COREDirectedModule)

COREMapKind = ct.c_int
COREMapKind_STR2TYPE_ORDEREDMAP = COREMapKind(0)
COREMapKind_STR2PARAM_MAP = COREMapKind(1)
COREMapKind_STR2ARG_MAP = COREMapKind(2)

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


class CoreIRType(object):
    def __init__(self, ptr, context):
        self.ptr = ptr
        assert isinstance(context,Context)
        self.context = context

class Params(CoreIRType):
    pass

class Args(CoreIRType):
    pass

class Type(CoreIRType):
    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintType(self.ptr)


class Wireable(CoreIRType):
    def get_connected_wireables(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetConnectedWireables(self.ptr, ct.byref(size))
        return [Wireable(result[i],self.context) for i in range(size.value)]

    def get_selectpath(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetSelectPath(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    def select(self, field):
        return Select(libcoreir_c.COREWireableSelect(self.ptr, str.encode(field)),self.context)

    def get_module_def(self):
        return ModuleDef(libcoreir_c.COREWireableGetModuleDef(self.ptr),self.context)

    def get_module(self):
        return self.get_module_def().get_module()


class Select(Wireable):
    pass
    # @property
    # def parent(self):
    #     return Wireable(libcoreir_c.CORESelectGetParent(self.ptr))


class Interface(Wireable):
    def select(self, field):
        return Select(libcoreir_c.COREInterfaceSelect(self.ptr, str.encode(field)),self.context)


class Connection(CoreIRType):
    @property
    def first(self):
        return Wireable(libcoreir_c.COREConnectionGetFirst(self.ptr), self.context)

    @property
    def second(self):
        return Wireable(libcoreir_c.COREConnectionGetSecond(self.ptr), self.context)


class Instance(Wireable):
    def select(self, field):
        return Select(libcoreir_c.COREInstanceSelect(self.ptr, str.encode(field)),self.context)
    
    def module_name(self):
        name = libcoreir_c.COREGetInstRefName(self.ptr)
        return name.decode()

    def get_config_value(self,key):
        arg = libcoreir_c.COREGetConfigValue(self.ptr,str.encode(key))
        #TODO this shoud be done better
        err = ct.c_bool(False)
        v = libcoreir_c.COREArg2Str(arg,ct.byref(err))
        if err.value==False:
          return v.decode()

        err = ct.c_bool(False)
        v = libcoreir_c.COREArg2Int(arg,ct.byref(err))
        if err.value==False:
          return v
        
        assert(False,"NYI!")

class ModuleDef(CoreIRType):
    def add_module_instance(self, name, module, config=None):
        if config==None:
            config = self.context.newArgs()
        assert isinstance(module,Module)
        assert isinstance(config,Args)
        return Instance(libcoreir_c.COREModuleDefAddModuleInstance(self.ptr, str.encode(name), module.ptr,config.ptr),self.context)

    def get_interface(self):
        return Interface(libcoreir_c.COREModuleDefGetInterface(self.ptr),self.context)

    def get_module(self):
        return Module(libcoreir_c.COREModuleDefGetModule(self.ptr),self.context)

    def get_instances(self):
        size = ct.c_int()
        result = libcoreir_c.COREModuleDefGetInstances(self.ptr, ct.byref(size))
        return [Instance(result[i],self.context) for i in range(size.value)]

    def get_connections(self):
        size = ct.c_int()
        result = libcoreir_c.COREModuleDefGetConnections(self.ptr, ct.byref(size))
        return [Connection(result[i], self.context) for i in range(size.value)]

    def connect(self, a, b):
        libcoreir_c.COREModuleDefConnect(self.ptr, a.ptr, b.ptr)

    def select(self, field):
        return Wireable(libcoreir_c.COREModuleDefSelect(self.ptr, str.encode(field)),self.context)

    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintModuleDef(self.ptr)


class Module(CoreIRType):
    def new_definition(self):
        return ModuleDef(libcoreir_c.COREModuleNewDef(self.ptr),self.context)

    def get_directed_module(self):
        return DirectedModule(libcoreir_c.COREModuleGetDirectedModule(self.ptr), self.context)

    def get_definition(self):
        return ModuleDef(libcoreir_c.COREModuleGetDef(self.ptr),self.context)

    def set_definition(self, definition):
        assert isinstance(definition, ModuleDef)
        libcoreir_c.COREModuleSetDef(self.ptr, definition.ptr)

    def save_to_file(self, file_name):
        err = ct.c_bool(False)
        assert (err.value ==False)
        print("Trying to save to file!\n")
        libcoreir_c.CORESaveModule(self.ptr, str.encode(file_name),ct.byref(err))
        assert(err.value==False)

    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintModule(self.ptr)

class Namespace(CoreIRType):
    @property
    def name(self):
        return libcoreir_c.CORENamespaceGetName(self.ptr).decode()

    def new_module(self, name, typ,cparams=None):
        assert isinstance(typ,Type)
        if cparams==None:
            cparams = self.context.newParams()
        assert isinstance(cparams,Params)
        return Module(libcoreir_c.CORENewModule(self.ptr, 
                                               ct.c_char_p(str.encode(name)), 
                                               typ.ptr,
                                               cparams.ptr),
                      self.context)


class Context:
    AINT=0
    ASTRING=1
    ATYPE=2
    def __init__(self):
        # FIXME: Rename this to ptr or context_ptr to be consistent with other
        #        API objects
        self.context = libcoreir_c.CORENewContext()
        self.G = Namespace(libcoreir_c.COREGetGlobal(self.context),self)
    
    def print_errors(self):
        libcoreir_c.COREPrintErrors(self.context)

    def GetG(self):
        return self.G
    
    def Any(self):
        return Type(libcoreir_c.COREAny(self.context),self)

    def BitIn(self):
        return Type(libcoreir_c.COREBitIn(self.context),self)

    def Bit(self):
        return Type(libcoreir_c.COREBit(self.context),self)

    def Array(self, length, typ):
        assert isinstance(typ, Type)
        assert isinstance(length, int)
        return Type(libcoreir_c.COREArray(self.context, length, typ.ptr),self)

    def Record(self, fields):
        keys = []
        values = []
        for key, value in fields.items():
            keys.append(str.encode(key))
            values.append(value.ptr)
        keys   = (ct.c_char_p * len(fields))(*keys)
        values = (COREType_p * len(fields))(*values)
        record_params = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2TYPE_ORDEREDMAP)
        return Type(libcoreir_c.CORERecord(self.context, record_params),self)

    def newParams(self, fields={}):
        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (ct.c_int * len(fields))(*(value for value in fields.values()))
        gen_params = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2PARAM_MAP)
        return Params(gen_params,self)
  
    def newArgs(self,fields={}):
        args = []
        for v in fields.values():
          if type(v) is int:
            args.append(libcoreir_c.COREInt2Arg(self.context,ct.c_int(v)))
          elif type(v) is str:
            args.append(libcoreir_c.COREStr2Arg(self.context,ct.c_char_p(str.encode(v))))
          else:
            assert(False,"NYI!")

        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (COREArg_p * len(fields))(*(arg for arg in args))
        gen_args = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2ARG_MAP)
        return Args(gen_args,self)

    def load_from_file(self, file_name):
        err = ct.c_bool(False)
        m = libcoreir_c.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name)),ct.byref(err))
        if (err.value):
           self.print_errors()

        return Module(m,self)

    def load_library(self, name):
        lib = load_shared_lib(name)
        func = getattr(lib,"CORELoadLibrary_{}".format(name))
        func.argtypes = [COREContext_p]
        func.restype = CORENamespace_p
        return Namespace(func(self.context), self)

    def __del__(self):
        libcoreir_c.COREDeleteContext(self.context)

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


class DirectedInstance(CoreIRType):
    def get_inputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedInstanceGetInputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    def get_outputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedInstanceGetOutputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]



class DirectedConnection(CoreIRType):
    @property
    def source(self):
        size = ct.c_int()
        result = libcoreir_c.COREDirectedConnectionGetSrc(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    @property
    def sink(self):
        size = ct.c_int()
        result = libcoreir_c.COREDirectedConnectionGetSnk(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

class DirectedModule(CoreIRType):
    def sel(self, path):
        arr = (ct.c_char_p * len(path))();
        for i, item in enumerate(path):
            arr[i] = item.encode()
        return Wireable(libcoreir_c.COREDirectedModuleSel(self.ptr, arr, len(path)), self.context)

    def get_connections(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetConnections(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    def get_inputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetInputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    def get_outputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetOutputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    def get_instances(self):
        num_instances = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetInstances(self.ptr, ct.byref(num_instances))
        return [DirectedInstance(result[i], self.context) for i in range(num_instances.value)]
