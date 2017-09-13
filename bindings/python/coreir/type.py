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

class Arg(CoreIRType):
    @property
    def value(self):
        type = libcoreir_c.COREGetArgKind(self.ptr)
        # type enum values defined in include/coreir-c/coreir-args.h
        if type == 0:
            return libcoreir_c.COREArgIntGet(self.ptr)
        elif type == 1:
            return libcoreir_c.COREArgStringGet(self.ptr).decode()
        elif type == 3:
            return libcoreir_c.COREArgBoolGet(self.ptr)
        raise NotImplementedError()

class Args(CoreIRType):
    pass

class Type(CoreIRType):
    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintType(self.ptr)
    
    @property
    def size(self):
        return libcoreir_c.CORETypeGetSize(self.ptr)

    @property
    def kind(self):
        # TypeKind enum defined in src/types.hpp
        kind = libcoreir_c.COREGetTypeKind(self.ptr)
        return {
            0: "Bit",
            1: "BitIn",
            2: "Array",
            3: "Record",
            4: "Named",
            5: "Any"
        }[kind]

    def __len__(self):
        if self.kind != "Array":  # Not a TK_Array
            raise Exception("`len` called on a {}".format(self.kind))
        return libcoreir_c.COREArrayTypeGetLen(self.ptr)
