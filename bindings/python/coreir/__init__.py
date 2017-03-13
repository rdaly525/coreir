from ctypes import cdll
import ctypes as ct
import platform
import os


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

class CORERecordParam(ct.Structure):
    pass

CORERecordParam_p = ct.POINTER(CORERecordParam)

class COREInstance(ct.Structure):
    pass

COREInstance_p = ct.POINTER(COREInstance)

class COREInterface(ct.Structure):
    pass

COREInterface_p = ct.POINTER(COREInterface)

class COREWireable(ct.Structure):
    pass

COREWireable_p = ct.POINTER(COREWireable)

class CORESelect(COREWireable):
    pass

CORESelect_p = ct.POINTER(CORESelect)

class COREConnection(ct.Structure):
    pass

COREConnection_p = ct.POINTER(COREConnection)

coreir_lib = load_shared_lib()

coreir_lib.CORENewContext.restype = COREContext_p

coreir_lib.COREAny.argtypes = [COREContext_p]
coreir_lib.COREAny.restype = COREType_p

coreir_lib.COREBitIn.argtypes = [COREContext_p]
coreir_lib.COREBitIn.restype = COREType_p

coreir_lib.COREBitOut.argtypes = [COREContext_p]
coreir_lib.COREBitOut.restype = COREType_p

coreir_lib.COREArray.argtypes = [COREContext_p, ct.c_uint32, COREType_p]
coreir_lib.COREArray.restype = COREType_p

coreir_lib.CORENewRecordParam.argtypes = [COREContext_p]
coreir_lib.CORENewRecordParam.restype = CORERecordParam_p

coreir_lib.CORERecordParamAddField.argtypes = [CORERecordParam_p, ct.c_char_p, COREType_p]

coreir_lib.CORERecord.argtypes = [COREContext_p, CORERecordParam_p]
coreir_lib.CORERecord.restype = COREType_p

coreir_lib.COREPrintType.argtypes = [COREType_p, ]

coreir_lib.CORELoadModule.argtypes = [COREContext_p, ct.c_char_p, ct.POINTER(ct.c_bool)]
coreir_lib.CORELoadModule.restype = COREModule_p

coreir_lib.CORESaveModule.argtypes = [COREModule_p, ct.c_char_p, ct.POINTER(ct.c_bool)]
#coreir_lib.CORESaveModule.restype = ct.c_bool

coreir_lib.COREGetGlobal.argtypes = [COREContext_p]
coreir_lib.COREGetGlobal.restype = CORENamespace_p

coreir_lib.CORENewModule.argtypes = [CORENamespace_p, ct.c_char_p, COREType_p]
coreir_lib.CORENewModule.restype = COREModule_p

coreir_lib.COREModuleAddDef.argtypes = [COREModule_p, COREModuleDef_p]

coreir_lib.COREPrintModule.argtypes = [COREModule_p]

coreir_lib.COREModuleNewDef.argtypes = [COREModule_p]
coreir_lib.COREModuleNewDef.restype = COREModuleDef_p

coreir_lib.COREModuleDefAddInstanceModule.argtypes = [COREModuleDef_p, ct.c_char_p, COREModule_p]
coreir_lib.COREModuleDefAddInstanceModule.restype = COREInstance_p

coreir_lib.COREModuleDefGetInterface.argtypes = [COREModuleDef_p]
coreir_lib.COREModuleDefGetInterface.restype = COREInterface_p

coreir_lib.COREModuleDefGetInstances.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
coreir_lib.COREModuleDefGetInstances.restype = ct.POINTER(COREInstance_p)

coreir_lib.COREModuleDefGetConnections.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
coreir_lib.COREModuleDefGetConnections.restype = ct.POINTER(COREConnection_p)

coreir_lib.COREModuleDefWire.argtypes = [COREModuleDef_p, COREWireable_p, COREWireable_p]

coreir_lib.COREInterfaceSelect.argtypes = [COREInterface_p, ct.c_char_p]
coreir_lib.COREInterfaceSelect.restype = CORESelect_p

coreir_lib.COREInstanceSelect.argtypes = [COREInstance_p, ct.c_char_p]
coreir_lib.COREInstanceSelect.restype = CORESelect_p

coreir_lib.COREPrintModuleDef.argtypes = [COREModuleDef_p]

coreir_lib.COREConnectionGetFirst.argtypes = [COREConnection_p]
coreir_lib.COREConnectionGetFirst.restyp = COREWireable_p

coreir_lib.COREConnectionGetSecond.argtypes = [COREConnection_p]
coreir_lib.COREConnectionGetSecond.restyp = COREWireable_p

coreir_lib.COREWireableGetConnectedWireables.argtypes = [COREWireable_p, ct.POINTER(ct.c_int)]
coreir_lib.COREWireableGetConnectedWireables.restype = ct.POINTER(COREWireable_p)

coreir_lib.COREWireableSelect.argtypes = [COREWireable_p, ct.c_char_p]
coreir_lib.COREWireableSelect.restyp = CORESelect_p

coreir_lib.COREModuleDefSelect.argtypes = [COREModuleDef_p, ct.c_char_p]
coreir_lib.COREModuleDefSelect.restyp = CORESelect_p

coreir_lib.CORESelectGetParent.argtypes = [CORESelect_p]
coreir_lib.CORESelectGetParent.restyp = COREWireable_p


class CoreIRType:
    def __init__(self, ptr):
        self.ptr = ptr


class Type(CoreIRType):
    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintType(self.ptr)


class Wireable(CoreIRType):
    def get_connected_wireables(self):
        size = ct.c_int()
        result = coreir_lib.COREWireableGetConnectedWireables(self.ptr, ct.byref(size))
        return [Wireable(result[i]) for i in range(size.value)]

    def select(self, field):
        return Select(coreir_lib.COREWireableSelect(self.ptr, str.encode(field)))


class Select(Wireable):
    @property
    def parent(self):
        return Wireable(coreir_lib.CORESelectGetParent(self.ptr))


class Interface(Wireable):
    def select(self, field):
        return Select(coreir_lib.COREInterfaceSelect(self.ptr, str.encode(field)))


class Connection(CoreIRType):
    @property
    def first(self):
        return Wireable(coreir_lib.COREConnectionGetFirst(self.ptr))

    @property
    def second(self):
        return Wireable(coreir_lib.COREConnectionGetSecond(self.ptr))


class Instance(Wireable):
    def select(self, field):
        return Select(coreir_lib.COREInstanceSelect(self.ptr, str.encode(field)))


class ModuleDef(CoreIRType):
    def add_instance_module(self, name, module):
        assert isinstance(module,Module)
        return Instance(coreir_lib.COREModuleDefAddInstanceModule(self.ptr, str.encode(name), module.ptr))

    def get_interface(self):
        return Interface(coreir_lib.COREModuleDefGetInterface(self.ptr))

    def get_instances(self):
        size = ct.c_int()
        result = coreir_lib.COREModuleDefGetInstances(self.ptr, ct.byref(size))
        return [Instance(result[i]) for i in range(size.value)]

    def get_connections(self):
        size = ct.c_int()
        result = coreir_lib.COREModuleDefGetConnections(self.ptr, ct.byref(size))
        return [Connection(result[i]) for i in range(size.value)]

    def wire(self, a, b):
        coreir_lib.COREModuleDefWire(self.ptr, a.ptr, b.ptr)

    def select(self, field):
        return Wireable(coreir_lib.COREModuleDefSelect(self.ptr, str.encode(field)))

    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintModuleDef(self.ptr)


class Module(CoreIRType):
    def new_definition(self):
        return ModuleDef(coreir_lib.COREModuleNewDef(self.ptr))

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
  def Module(self, name, typ):
    return Module(
      coreir_lib.CORENewModule(self.ptr, ct.c_char_p(str.encode(name)), typ.ptr))

class Context:
    def __init__(self):
        self.context = coreir_lib.CORENewContext()
        self.G = Namespace(coreir_lib.COREGetGlobal(self.context))
    
    def GetG(self):
      return Namespace(coreir_lib.COREGetGlobal(self.context))
    
    def Any(self):
        return Type(coreir_lib.COREAny(self.context))

    def BitIn(self):
        return Type(coreir_lib.COREBitIn(self.context))

    def BitOut(self):
        return Type(coreir_lib.COREBitOut(self.context))

    def Array(self, length, typ):
        assert isinstance(typ, Type)
        assert isinstance(length, int)
        return Type(coreir_lib.COREArray(self.context, length, typ.ptr))

    def load_from_file(self, file_name):
        err = ct.c_bool(False)
        m = coreir_lib.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name)),ct.byref(err))
        assert not err.value
        return Module(m)
 
    def Record(self, fields):
        record_params = coreir_lib.CORENewRecordParam(self.context)
        for key, value in fields.items():
            coreir_lib.CORERecordParamAddField(record_params, str.encode(key), value.ptr)
        return Type(coreir_lib.CORERecord(self.context, record_params))

    def __del__(self):
        coreir_lib.COREDeleteContext(self.context)

