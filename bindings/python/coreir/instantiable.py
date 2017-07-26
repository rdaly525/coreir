import ctypes as ct
from coreir.type import CoreIRType, Type, Params
from coreir.module import Module
from coreir.lib import libcoreir_c

class COREInstantiable(ct.Structure):
    pass

COREInstantiable_p = ct.POINTER(COREInstantiable)


class Instantiable(CoreIRType):
    @property
    def name(self):
        return libcoreir_c.COREInstantiableGetName(self.ptr).decode()

    @property
    def kind(self):
        kind = libcoreir_c.COREInstantiableGetKind(self.ptr)
        if kind == 0:
            return Module
        elif kind == 1:
            return Generator
        raise NotImplementedError()


class Generator(Instantiable):
    pass
