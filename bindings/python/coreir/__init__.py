from ctypes import cdll
import ctypes as ct
import platform
import os
from collections import namedtuple

def load_shared_lib():
    _system = platform.system()
    if _system == "Linux":
        shared_lib_ext = "so"
    elif _system == "Darwin":
        shared_lib_ext = "dylib"
    else:
        raise NotImplementedError(_system)

    dir_path = os.path.dirname(os.path.realpath(__file__))

    return cdll.LoadLibrary('{}/../../../build/coreir.{}'.format(dir_path, shared_lib_ext))

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

COREMapKind = ct.c_int
COREMapKind_STR2TYPE_ORDEREDMAP = COREMapKind(0)
COREMapKind_STR2PARAM_MAP = COREMapKind(1)
COREMapKind_STR2ARG_MAP = COREMapKind(2)

coreir_lib = load_shared_lib()

coreir_lib.CORENewMap.argtypes = [COREContext_p, ct.c_void_p, ct.c_void_p, ct.c_uint32, COREMapKind]

coreir_lib.CORENewMap.restype = ct.c_void_p

coreir_lib.CORENewContext.restype = COREContext_p

coreir_lib.COREPrintErrors.argtypes = [COREContext_p]

coreir_lib.COREAny.argtypes = [COREContext_p]
coreir_lib.COREAny.restype = COREType_p

coreir_lib.COREBitIn.argtypes = [COREContext_p]
coreir_lib.COREBitIn.restype = COREType_p

coreir_lib.COREBitOut.argtypes = [COREContext_p]
coreir_lib.COREBitOut.restype = COREType_p

coreir_lib.COREArray.argtypes = [COREContext_p, ct.c_uint32, COREType_p]
coreir_lib.COREArray.restype = COREType_p

coreir_lib.CORERecord.argtypes = [COREContext_p, ct.c_void_p]
coreir_lib.CORERecord.restype = COREType_p

coreir_lib.COREPrintType.argtypes = [COREType_p, ]

coreir_lib.CORELoadModule.argtypes = [COREContext_p, ct.c_char_p, ct.POINTER(ct.c_bool)]
coreir_lib.CORELoadModule.restype = COREModule_p

coreir_lib.CORESaveModule.argtypes = [COREModule_p, ct.c_char_p, ct.POINTER(ct.c_bool)]

coreir_lib.COREGetGlobal.argtypes = [COREContext_p]
coreir_lib.COREGetGlobal.restype = CORENamespace_p

coreir_lib.CORENewModule.argtypes = [CORENamespace_p, ct.c_char_p, COREType_p, ct.c_void_p]
coreir_lib.CORENewModule.restype = COREModule_p

coreir_lib.COREModuleAddDef.argtypes = [COREModule_p, COREModuleDef_p]

coreir_lib.COREPrintModule.argtypes = [COREModule_p]

coreir_lib.COREModuleNewDef.argtypes = [COREModule_p]
coreir_lib.COREModuleNewDef.restype = COREModuleDef_p

coreir_lib.COREModuleGetDef.argtypes = [COREModule_p]
coreir_lib.COREModuleGetDef.restype = COREModuleDef_p

coreir_lib.COREModuleDefAddModuleInstance.argtypes = [COREModuleDef_p, ct.c_char_p, COREModule_p, ct.c_void_p]
coreir_lib.COREModuleDefAddModuleInstance.restype = COREInstance_p

coreir_lib.COREModuleDefGetInterface.argtypes = [COREModuleDef_p]
coreir_lib.COREModuleDefGetInterface.restype = COREInterface_p

coreir_lib.COREModuleDefGetInstances.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
coreir_lib.COREModuleDefGetInstances.restype = ct.POINTER(COREInstance_p)

coreir_lib.COREGetInstRefName.argtypes = [COREInstance_p]
coreir_lib.COREGetInstRefName.restype = ct.c_char_p

coreir_lib.COREGetConfigValue.argtypes = [COREInstance_p,ct.c_char_p]
coreir_lib.COREGetConfigValue.restype = COREArg_p;

coreir_lib.COREArg2Str.argtypes = [COREArg_p]
coreir_lib.COREArg2Str.restype = ct.c_char_p

coreir_lib.COREArg2Int.argtypes = [COREArg_p]
coreir_lib.COREArg2Int.restype = ct.c_int

coreir_lib.COREInt2Arg.argtypes = [COREContext_p,ct.c_int]
coreir_lib.COREInt2Arg.restype = COREArg_p

coreir_lib.COREStr2Arg.argtypes = [COREContext_p,ct.c_char_p]
coreir_lib.COREStr2Arg.restype = COREArg_p

# coreir_lib.COREModuleDefGetConnections.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
# coreir_lib.COREModuleDefGetConnections.restype = ct.POINTER(COREConnection_p)

coreir_lib.COREModuleDefWire.argtypes = [COREModuleDef_p, COREWireable_p, COREWireable_p]

coreir_lib.COREInterfaceSelect.argtypes = [COREInterface_p, ct.c_char_p]
coreir_lib.COREInterfaceSelect.restype = CORESelect_p

coreir_lib.COREInstanceSelect.argtypes = [COREInstance_p, ct.c_char_p]
coreir_lib.COREInstanceSelect.restype = CORESelect_p

coreir_lib.COREPrintModuleDef.argtypes = [COREModuleDef_p]

coreir_lib.COREConnectionGetFirst.argtypes = [COREConnection_p]
coreir_lib.COREConnectionGetFirst.restype = COREWireable_p

coreir_lib.COREConnectionGetSecond.argtypes = [COREConnection_p]
coreir_lib.COREConnectionGetSecond.restype = COREWireable_p

coreir_lib.COREWireableGetConnectedWireables.argtypes = [COREWireable_p, ct.POINTER(ct.c_int)]
coreir_lib.COREWireableGetConnectedWireables.restype = ct.POINTER(COREWireable_p)

coreir_lib.COREWireableGetModuleDef.argtypes = [COREWireable_p]
coreir_lib.COREWireableGetModuleDef.restype = COREModuleDef_p

coreir_lib.COREWireableSelect.argtypes = [COREWireable_p, ct.c_char_p]
coreir_lib.COREWireableSelect.restype = CORESelect_p

coreir_lib.COREWireableGetAncestors.argtypes = [COREWireable_p, ct.POINTER(ct.c_int)]
coreir_lib.COREWireableGetAncestors.restype = ct.POINTER(ct.c_char_p)

coreir_lib.COREModuleDefSelect.argtypes = [COREModuleDef_p, ct.c_char_p]
coreir_lib.COREModuleDefSelect.restype = CORESelect_p

coreir_lib.COREModuleDefGetModule.argtypes = [COREModuleDef_p]
coreir_lib.COREModuleDefGetModule.restype = COREModule_p

# coreir_lib.CORESelectGetParent.argtypes = [CORESelect_p]
# coreir_lib.CORESelectGetParent.restype = COREWireable_p


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
        coreir_lib.COREPrintType(self.ptr)


class Wireable(CoreIRType):
    def get_connected_wireables(self):
        size = ct.c_int()
        result = coreir_lib.COREWireableGetConnectedWireables(self.ptr, ct.byref(size))
        return [Wireable(result[i],self.context) for i in range(size.value)]

    def get_ancestors(self):
        size = ct.c_int()
        result = coreir_lib.COREWireableGetAncestors(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    def select(self, field):
        return Select(coreir_lib.COREWireableSelect(self.ptr, str.encode(field)),self.context)

    def get_module_def(self):
        return ModuleDef(coreir_lib.COREWireableGetModuleDef(self.ptr),self.context)

    def get_module(self):
        return self.get_module_def().get_module()


class Select(Wireable):
    pass
    # @property
    # def parent(self):
    #     return Wireable(coreir_lib.CORESelectGetParent(self.ptr))


class Interface(Wireable):
    def select(self, field):
        return Select(coreir_lib.COREInterfaceSelect(self.ptr, str.encode(field)),self.context)


class Connection(CoreIRType):
    @property
    def first(self):
        return Wireable(coreir_lib.COREConnectionGetFirst(self.ptr),self.context)

    @property
    def second(self):
        return Wireable(coreir_lib.COREConnectionGetSecond(self.ptr),self.context)


class Instance(Wireable):
    def select(self, field):
        return Select(coreir_lib.COREInstanceSelect(self.ptr, str.encode(field)),self.context)
    
    def module_name(self):
        name = coreir_lib.COREGetInstRefName(self.ptr)
        return str.decode(name)

    def get_config_value(self,key):
        arg = coreir_lib.COREGetConfigValue(self.ptr,str.encode(key))
        #TODO this shoud be done better
        err = ct.c_bool(False)
        v = coreir_lib.COREArg2Str(arg,ct.byref(err))
        if err.value==False:
          return str.decode(v)

        err = ct.c_bool(False)
        v = coreir_lib.COREArg2Int(arg,ct.byref(err))
        if err.value==False:
          print(type(v))
          return v

        assert(False,"NYI!")

class ModuleDef(CoreIRType):
    def add_module_instance(self, name, module, config=None):
        if config==None:
            config = self.context.newArgs()
        assert isinstance(module,Module)
        assert isinstance(config,Args)
        return Instance(coreir_lib.COREModuleDefAddModuleInstance(self.ptr, str.encode(name), module.ptr,config.ptr),self.context)

    def get_interface(self):
        return Interface(coreir_lib.COREModuleDefGetInterface(self.ptr),self.context)

    def get_module(self):
        return Module(coreir_lib.COREModuleDefGetModule(self.ptr),self.context)

    def get_instances(self):
        size = ct.c_int()
        result = coreir_lib.COREModuleDefGetInstances(self.ptr, ct.byref(size))
        return [Instance(result[i],self.context) for i in range(size.value)]

    # def get_connections(self):
    #     size = ct.c_int()
    #     result = coreir_lib.COREModuleDefGetConnections(self.ptr, ct.byref(size))
    #     return [Connection(result[i]) for i in range(size.value)]

    def wire(self, a, b):
        coreir_lib.COREModuleDefWire(self.ptr, a.ptr, b.ptr)

    def select(self, field):
        return Wireable(coreir_lib.COREModuleDefSelect(self.ptr, str.encode(field)),self.context)

    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintModuleDef(self.ptr)


class Module(CoreIRType):
    def new_definition(self):
        return ModuleDef(coreir_lib.COREModuleNewDef(self.ptr),self.context)

    def get_definition(self):
        return ModuleDef(coreir_lib.COREModuleGetDef(self.ptr),self.context)

    def add_definition(self, definition):
        assert isinstance(definition, ModuleDef)
        coreir_lib.COREModuleAddDef(self.ptr, definition.ptr)

    def save_to_file(self, file_name):
        err = ct.c_bool(False)
        assert (err.value ==False)
        print("Trying to save to file!\n")
        coreir_lib.CORESaveModule(self.ptr, str.encode(file_name),ct.byref(err))
        assert(err.value==False)

    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintModule(self.ptr)

class Namespace(CoreIRType):
  def new_module(self, name, typ,cparams=None):
    assert isinstance(typ,Type)
    if cparams==None:
      cparams = self.context.newParams()
    assert isinstance(cparams,Params)
    return Module(
      coreir_lib.CORENewModule(self.ptr, ct.c_char_p(str.encode(name)), typ.ptr,cparams.ptr),self.context)

class Context:
    AINT=0
    ASTRING=1
    ATYPE=2
    def __init__(self):
        self.context = coreir_lib.CORENewContext()
        self.G = Namespace(coreir_lib.COREGetGlobal(self.context),self)
    
    def print_errors(self):
        coreir_lib.COREPrintErrors(self.context)

    def GetG(self):
        return self.G
    
    def Any(self):
        return Type(coreir_lib.COREAny(self.context),self)

    def BitIn(self):
        return Type(coreir_lib.COREBitIn(self.context),self)

    def BitOut(self):
        return Type(coreir_lib.COREBitOut(self.context),self)

    def Array(self, length, typ):
        assert isinstance(typ, Type)
        assert isinstance(length, int)
        return Type(coreir_lib.COREArray(self.context, length, typ.ptr),self)

    def Record(self, fields):
        keys = []
        values = []
        for key, value in fields.items():
            keys.append(str.encode(key))
            values.append(value.ptr)
        keys   = (ct.c_char_p * len(fields))(*keys)
        values = (COREType_p * len(fields))(*values)
        record_params = coreir_lib.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2TYPE_ORDEREDMAP)
        return Type(coreir_lib.CORERecord(self.context, record_params),self)

    def newParams(self, fields={}):
        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (ct.c_int * len(fields))(*(value for value in fields.values()))
        gen_params = coreir_lib.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2PARAM_MAP)
        return Params(gen_params,self)
  
    def newArgs(self,fields={}):
        args = []
        for v in fields.values():
          if type(v) is int:
            args.append(coreir_lib.COREInt2Arg(self.context,ct.c_int(v)))
          elif type(v) is str:
            args.append(coreir_lib.COREStr2Arg(self.context,ct.c_char_p(str.encode(v))))
          else:
            assert(False,"NYI!")

        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (COREArg_p * len(fields))(*(arg for arg in args))
        gen_args = coreir_lib.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2ARG_MAP)
        return Args(gen_args,self)

    def load_from_file(self, file_name):
        err = ct.c_bool(False)
        m = coreir_lib.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name)),ct.byref(err))
        if (err.value):
           self.print_errors()

        return Module(m,self)

    def __del__(self):
        coreir_lib.COREDeleteContext(self.context)
