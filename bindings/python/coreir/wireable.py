import ctypes as ct
from coreir.base import CoreIRType
from coreir.lib import libcoreir_c
from coreir.type import Type
import coreir.module

class COREWireable(ct.Structure):
    pass

COREWireable_p = ct.POINTER(COREWireable)


class Wireable(CoreIRType):
    @property
    def connected_wireables(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetConnectedWireables(self.ptr, ct.byref(size))
        return [Wireable(result[i],self.context) for i in range(size.value)]

    @property
    def selectpath(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetSelectPath(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    def select(self, field):
        return Select(libcoreir_c.COREWireableSelect(self.ptr, str.encode(field)),self.context)

    @property
    def module_def(self):
        return coreir.module.ModuleDef(libcoreir_c.COREWireableGetModuleDef(self.ptr),self.context)

    @property
    def module(self):
        return self.module_def.module

    @property
    def type(self):
        return Type(libcoreir_c.COREWireableGetType(self.ptr), self.context)


class Select(Wireable):
    pass
    # @property
    # def parent(self):
    #     return Wireable(libcoreir_c.CORESelectGetParent(self.ptr))


class Instance(Wireable):
    @property
    def module_name(self):
        name = libcoreir_c.COREGetInstRefName(self.ptr)
        return name.decode()

    def get_config_value(self,key):
        arg = libcoreir_c.COREGetConfigValue(self.ptr,str.encode(key))
        type = libcoreir_c.COREGetArgKind(arg)
        # type enum values defined in include/coreir-c/coreir-args.h
        if type == 0:
            return libcoreir_c.COREArgIntGet(arg)
        elif type == 1:
            return libcoreir_c.COREArgStringGet(arg).decode()
        
        raise NotImplementedError


class Interface(Wireable):
    pass


class Connection(CoreIRType):
    @property
    def first(self):
        return Wireable(libcoreir_c.COREConnectionGetFirst(self.ptr), self.context)

    @property
    def second(self):
        return Wireable(libcoreir_c.COREConnectionGetSecond(self.ptr), self.context)
