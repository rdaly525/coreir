import ctypes as ct
from coreir.type import CoreIRType, Type, Params
from coreir.module import Module
from coreir.lib import libcoreir_c

class CORENamespace(ct.Structure):
    pass

CORENamespace_p = ct.POINTER(CORENamespace)


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
