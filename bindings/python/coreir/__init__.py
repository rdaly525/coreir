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

class EmptyStruct(ct.Structure):
    pass

# Pointers to typedefs use an empty struct as a placeholder
COREContext_p = ct.POINTER(EmptyStruct)
CORENamespace_p = ct.POINTER(EmptyStruct)
COREType_p = ct.POINTER(EmptyStruct)
COREModule_p = ct.POINTER(EmptyStruct)
COREModuleDef_p = ct.POINTER(EmptyStruct)
CORERecordParam_p = ct.POINTER(EmptyStruct)
COREInstance_p = ct.POINTER(EmptyStruct)
COREInterface_p = ct.POINTER(EmptyStruct)
CORESelect_p = ct.POINTER(EmptyStruct)
COREWireable_p = ct.POINTER(EmptyStruct)
COREWiring = EmptyStruct

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

coreir_lib.CORERecordParamAddField.argtypes = [COREContext_p, ct.c_char_p, COREType_p]

coreir_lib.CORERecord.argtypes = [COREContext_p, CORERecordParam_p]
coreir_lib.CORERecord.restype = COREType_p

coreir_lib.COREPrintType.argtypes = [COREType_p, ]

coreir_lib.CORELoadModule.argtypes = [COREContext_p, ct.c_char_p]
coreir_lib.CORELoadModule.restype = COREModule_p

coreir_lib.CORESaveModule.argtypes = [COREModule_p, ct.c_char_p]
coreir_lib.CORESaveModule.restype = ct.c_bool

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

coreir_lib.COREModuleDefGetWires.argtypes = [COREModuleDef_p, ct.POINTER(ct.c_int)]
coreir_lib.COREModuleDefGetWires.restype = ct.POINTER(COREWiring)

coreir_lib.COREModuleDefWire.argtypes = [COREModuleDef_p, COREWireable_p, COREWireable_p]

coreir_lib.COREInterfaceSelect.argtypes = [COREInterface_p, ct.c_char_p]
coreir_lib.COREInterfaceSelect.restype = CORESelect_p

coreir_lib.COREInstanceSelect.argtypes = [COREInstance_p, ct.c_char_p]
coreir_lib.COREInstanceSelect.restype = CORESelect_p

coreir_lib.COREPrintModuleDef.argtypes = [COREModuleDef_p]


class CoreIRType:
    def __init__(self, ptr):
        self.ptr = ptr


class Type(CoreIRType):
    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintType(self.ptr)


class Select(CoreIRType):
    pass


class Interface(CoreIRType):
    def select(self, field):
        return Select(coreir_lib.COREInterfaceSelect(self.ptr, str.encode(field)))


class Wiring(CoreIRType):
    pass


class Instance(CoreIRType):
    def select(self, field):
        return Select(coreir_lib.COREInterfaceSelect(self.ptr, str.encode(field)))


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

    def get_wires(self):
        size = ct.c_int()
        result = coreir_lib.COREModuleDefGetWires(self.ptr, ct.byref(size))
        return [Wiring(result[i]) for i in range(size.value)]

    def wire(self, a, b):
        coreir_lib.COREModuleDefWire(self.ptr, a.ptr, b.ptr)

    def print_(self):  # _ because print is a keyword in py2
        coreir_lib.COREPrintModuleDef(self.ptr)


class Module(CoreIRType):
    def new_definition(self):
        return ModuleDef(coreir_lib.COREModuleNewDef(self.ptr))

    def add_definition(self, definition):
        assert isinstance(definition, ModuleDef)
        coreir_lib.COREModuleAddDef(self.ptr, definition.ptr)

    def save_to_file(self, file_name):
        coreir_lib.CORESaveModule(self.ptr, str.encode(file_name))

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

    def ModuleFromFile(self, file_name):
        return Module(
            coreir_lib.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name))))

 
    def Record(self, fields):
        record_params = coreir_lib.CORENewRecordParam(self.context)
        for key, value in fields.items():
            coreir_lib.CORERecordParamAddField(record_params, str.encode(key), value.ptr)
        return Type(coreir_lib.CORERecord(self.context, record_params))

    def __del__(self):
        coreir_lib.COREDeleteContext(self.context)

