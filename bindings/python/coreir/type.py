import ctypes as ct
from coreir.base import CoreIRType

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
