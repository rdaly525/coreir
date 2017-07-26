import ctypes as ct
from coreir.type import CoreIRType, Type, Params
from coreir.module import Module
from coreir.lib import libcoreir_c
from coreir.instantiable import Instantiable, Generator
from coreir.util import LazyDict

class CORENamespace(ct.Structure):
    pass

CORENamespace_p = ct.POINTER(CORENamespace)


class Namespace(CoreIRType):
    def __init__(self, ptr, context):
        super(Namespace, self).__init__(ptr, context)
        self.instantiables = LazyDict(self, Instantiable, libcoreir_c.CORENamespaceGetInstantiable)
        self.generators = LazyDict(self, Generator, libcoreir_c.CORENamespaceGetGenerator)
        self.modules = LazyDict(self, Module, libcoreir_c.CORENamespaceGetModule)

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
