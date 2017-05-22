import ctypes as ct
from coreir.base import CoreIRType
from coreir.lib import libcoreir_c
import coreir.module

class COREWireable(ct.Structure):
    pass

COREWireable_p = ct.POINTER(COREWireable)


class Wireable(CoreIRType):
    def get_connected_wireables(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetConnectedWireables(self.ptr, ct.byref(size))
        return [Wireable(result[i],self.context) for i in range(size.value)]

    def get_selectpath(self):
        size = ct.c_int()
        result = libcoreir_c.COREWireableGetSelectPath(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    def select(self, field):
        return Select(libcoreir_c.COREWireableSelect(self.ptr, str.encode(field)),self.context)

    def get_module_def(self):
        return coreir.module.ModuleDef(libcoreir_c.COREWireableGetModuleDef(self.ptr),self.context)

    def get_module(self):
        return self.get_module_def().get_module()


class CORESelect(COREWireable):
    pass

CORESelect_p = ct.POINTER(CORESelect)


class Select(Wireable):
    pass
    # @property
    # def parent(self):
    #     return Wireable(libcoreir_c.CORESelectGetParent(self.ptr))


class COREInstance(COREWireable):
    pass

COREInstance_p = ct.POINTER(COREInstance)


class Instance(Wireable):
    def select(self, field):
        return Select(libcoreir_c.COREInstanceSelect(self.ptr, str.encode(field)),self.context)
    
    def module_name(self):
        name = libcoreir_c.COREGetInstRefName(self.ptr)
        return name.decode()

    def get_config_value(self,key):
        arg = libcoreir_c.COREGetConfigValue(self.ptr,str.encode(key))
        #TODO this shoud be done better
        err = ct.c_bool(False)
        v = libcoreir_c.COREArg2Str(arg,ct.byref(err))
        if err.value==False:
          return v.decode()

        err = ct.c_bool(False)
        v = libcoreir_c.COREArg2Int(arg,ct.byref(err))
        if err.value==False:
          return v
        
        raise NotImplementedError

class COREInterface(COREWireable):
    pass

COREInterface_p = ct.POINTER(COREInterface)


class Interface(Wireable):
    def select(self, field):
        return Select(libcoreir_c.COREInterfaceSelect(self.ptr, str.encode(field)),self.context)


class Connection(CoreIRType):
    @property
    def first(self):
        return Wireable(libcoreir_c.COREConnectionGetFirst(self.ptr), self.context)

    @property
    def second(self):
        return Wireable(libcoreir_c.COREConnectionGetSecond(self.ptr), self.context)
