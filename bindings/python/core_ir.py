from ctypes import cdll
import ctypes as ct
import platform


def load_shared_lib():
    _system = platform.system()

    if _system == "Linux":
        shared_lib_ext = "so"
    elif _system == "Darwin":
        shared_lib_ext = "dylib"
    else:
        raise NotImplementedError(_system)

    return cdll.LoadLibrary('../../src/coreir.{}'.format(shared_lib_ext))

class EmptyStruct(ct.Structure):
    pass

# Pointers to typedefs use an empty struct as a placeholder
COREContext_p = ct.POINTER(EmptyStruct)
COREType_p = ct.POINTER(EmptyStruct)
COREModule_p = ct.POINTER(EmptyStruct)
COREModuleDef_p = ct.POINTER(EmptyStruct)

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
coreir_lib.COREPrintType.argtypes = [COREType_p, ]
coreir_lib.CORELoadModule.argtypes = [COREContext_p, ct.c_char_p]
coreir_lib.CORELoadModule.restype = COREModule_p
coreir_lib.COREPrintModule.argtypes = [COREModule_p]


class Type:
    def __init__(self, type):
        self.type = type

    def print(self):
        coreir_lib.COREPrintType(self.type)


class Module:
    def __init__(self, module):
        self.module = module

    def print(self):
        coreir_lib.COREPrintModule(self.module)


class Context:
    def __init__(self):
        self.context = coreir_lib.CORENewContext()

    def Any(self):
        return Type(coreir_lib.COREAny(self.context))

    def BitIn(self):
        return Type(coreir_lib.COREBitIn(self.context))

    def BitOut(self):
        return Type(coreir_lib.COREBitOut(self.context))

    def Array(self, len, type):
        assert isinstance(type, Type)
        assert isinstance(len, int)
        return Type(coreir_lib.COREArray(self.context, len, type.type))

    def Module(self, file_name):
        return Module(
            coreir_lib.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name))))

    def __del__(self):
        coreir_lib.COREDeleteContext(self.context)

if __name__ == "__main__":
    c = Context()
    any = c.Any()
    any.print()
    c.BitIn().print()
    c.BitOut().print()
    c.Array(3, c.BitIn()).print()

    c.Array(3, c.Array(4, c.BitIn())).print()

    c.Module("test").print()
