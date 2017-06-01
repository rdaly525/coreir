import ctypes as ct
from coreir.base import CoreIRType
from coreir.lib import libcoreir_c

class COREType(ct.Structure):
    pass

COREType_p = ct.POINTER(COREType)

class Params(CoreIRType):
    pass

class COREArg(ct.Structure):
  pass

COREArg_p = ct.POINTER(COREArg)

class Args(CoreIRType):
    pass

class Type(CoreIRType):
    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintType(self.ptr)

    def __len__(self):
        # TypeKind enum defined in src/types.hpp
        kind = libcoreir_c.COREGetTypeKind(self.ptr)
        if kind != 2:  # Not a TK_Array
            type_name = {
                0: "Bit",
                1: "BitIn",
                3: "Record",
                4: "Named",
                5: "Any"
            }[kind]
            raise Exception("`len` called on a non Array Type ({})".format(type_name))
        return libcoreir_c.COREArrayTypeGetLen(self.ptr)
