import ctypes as ct
from coreir.type import CoreIRType, Args
from coreir.lib import libcoreir_c
from coreir.wireable import Instance, Interface
import coreir.wireable


class COREModule(ct.Structure):
    pass

COREModule_p = ct.POINTER(COREModule)

class COREModuleDef(ct.Structure):
    pass

COREModuleDef_p = ct.POINTER(COREModuleDef)


class ModuleDef(CoreIRType):
    def add_module_instance(self, name, module, config=None):
        if config==None:
            config = self.context.newArgs()
        assert isinstance(module,Module)
        assert isinstance(config,Args)
        return Instance(libcoreir_c.COREModuleDefAddModuleInstance(self.ptr, str.encode(name), module.ptr,config.ptr),self.context)

    @property
    def interface(self):
        return Interface(libcoreir_c.COREModuleDefGetInterface(self.ptr),self.context)

    @property
    def module(self):
        # TODO: Probably a better name for this function?
        return Module(libcoreir_c.COREModuleDefGetModule(self.ptr),self.context)

    @property
    def instances(self):
        size = ct.c_int()
        result = libcoreir_c.COREModuleDefGetInstances(self.ptr, ct.byref(size))
        return [Instance(result[i],self.context) for i in range(size.value)]

    @property
    def connections(self):
        size = ct.c_int()
        result = libcoreir_c.COREModuleDefGetConnections(self.ptr, ct.byref(size))
        return [coreir.wireable.Connection(result[i], self.context) for i in range(size.value)]

    def connect(self, a, b):
        libcoreir_c.COREModuleDefConnect(self.ptr, a.ptr, b.ptr)

    def select(self, field):
        return coreir.wireable.Wireable(libcoreir_c.COREModuleDefSelect(self.ptr, str.encode(field)),self.context)

    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintModuleDef(self.ptr)


class Module(CoreIRType):
    def new_definition(self):
        return ModuleDef(libcoreir_c.COREModuleNewDef(self.ptr),self.context)

    @property
    def directed_module(self):
        return DirectedModule(libcoreir_c.COREModuleGetDirectedModule(self.ptr), self.context)

    @property
    def definition(self):
        return ModuleDef(libcoreir_c.COREModuleGetDef(self.ptr),self.context)

    @definition.setter
    def definition(self, definition):
        assert isinstance(definition, ModuleDef)
        libcoreir_c.COREModuleSetDef(self.ptr, definition.ptr)

    def save_to_file(self, file_name):
        err = ct.c_bool(False)
        assert (err.value ==False)
        print("Trying to save to file!\n")
        libcoreir_c.CORESaveModule(self.ptr, str.encode(file_name),ct.byref(err))
        assert(err.value==False)

    def print_(self):  # _ because print is a keyword in py2
        libcoreir_c.COREPrintModule(self.ptr)


class COREDirectedInstance(ct.Structure):
    pass

COREDirectedInstance_p = ct.POINTER(COREDirectedInstance)

class COREDirectedConnection(ct.Structure):
    pass

COREDirectedConnection_p = ct.POINTER(COREDirectedConnection)

class COREDirectedModule(ct.Structure):
    pass

COREDirectedModule_p = ct.POINTER(COREDirectedModule)

class DirectedInstance(CoreIRType):
    @property
    def inputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedInstanceGetInputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    @property
    def outputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedInstanceGetOutputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]



class DirectedConnection(CoreIRType):
    @property
    def source(self):
        size = ct.c_int()
        result = libcoreir_c.COREDirectedConnectionGetSrc(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

    @property
    def sink(self):
        size = ct.c_int()
        result = libcoreir_c.COREDirectedConnectionGetSnk(self.ptr, ct.byref(size))
        return [result[i].decode() for i in range(size.value)]

class DirectedModule(CoreIRType):
    def sel(self, path):
        arr = (ct.c_char_p * len(path))();
        for i, item in enumerate(path):
            arr[i] = item.encode()
        return coreir.wireable.Wireable(libcoreir_c.COREDirectedModuleSel(self.ptr, arr, len(path)), self.context)

    @property
    def connections(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetConnections(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    @property
    def inputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetInputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    @property
    def outputs(self):
        num_connections = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetOutputs(self.ptr, ct.byref(num_connections))
        return [DirectedConnection(result[i], self.context) for i in range(num_connections.value)]

    @property
    def instances(self):
        num_instances = ct.c_int()
        result = libcoreir_c.COREDirectedModuleGetInstances(self.ptr, ct.byref(num_instances))
        return [DirectedInstance(result[i], self.context) for i in range(num_instances.value)]
