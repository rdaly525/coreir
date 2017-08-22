import ctypes as ct
from coreir.type import COREType_p, Type, Params, COREArg_p, Args
from coreir.namespace import Namespace, CORENamespace_p
from coreir.lib import libcoreir_c, load_shared_lib
import coreir.module

class COREContext(ct.Structure):
    pass

COREContext_p = ct.POINTER(COREContext)

COREMapKind = ct.c_int
COREMapKind_STR2TYPE_ORDEREDMAP = COREMapKind(0)
COREMapKind_STR2PARAM_MAP = COREMapKind(1)
COREMapKind_STR2ARG_MAP = COREMapKind(2)


class Context:
    AINT=0
    ASTRING=1
    ATYPE=2
    def __init__(self):
        # FIXME: Rename this to ptr or context_ptr to be consistent with other
        #        API objects
        self.context = libcoreir_c.CORENewContext()
        self.G = Namespace(libcoreir_c.COREGetGlobal(self.context),self)
    
    def print_errors(self):
        libcoreir_c.COREPrintErrors(self.context)
    
    def Any(self):
        return Type(libcoreir_c.COREAny(self.context),self)

    def BitIn(self):
        return Type(libcoreir_c.COREBitIn(self.context),self)

    def Bit(self):
        return Type(libcoreir_c.COREBit(self.context),self)

    def Array(self, length, typ):
        assert isinstance(typ, Type)
        assert isinstance(length, int)
        return Type(libcoreir_c.COREArray(self.context, length, typ.ptr),self)

    def Record(self, fields):
        keys = []
        values = []
        for key, value in fields.items():
            keys.append(str.encode(key))
            values.append(value.ptr)
        keys   = (ct.c_char_p * len(fields))(*keys)
        values = (COREType_p * len(fields))(*values)
        record_params = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2TYPE_ORDEREDMAP)
        return Type(libcoreir_c.CORERecord(self.context, record_params),self)

    def newParams(self, fields={}):
        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (ct.c_int * len(fields))(*(value for value in fields.values()))
        gen_params = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2PARAM_MAP)
        return Params(gen_params,self)
  
    def newArgs(self,fields={}):
        args = []
        for v in fields.values():
          if type(v) is int:
            args.append(libcoreir_c.COREArgInt(self.context,ct.c_int(v)))
          elif type(v) is str:
            args.append(libcoreir_c.COREArgString(self.context,ct.c_char_p(str.encode(v))))
          elif type(v) is bool:
            args.append(libcoreir_c.COREArgBool(self.context,v))
          else:
            raise NotImplementedError()

        keys = (ct.c_char_p * len(fields))(*(str.encode(key) for key in fields.keys()))
        values = (COREArg_p * len(fields))(*(arg for arg in args))
        gen_args = libcoreir_c.CORENewMap(self.context, ct.cast(keys,
            ct.c_void_p), ct.cast(values, ct.c_void_p), len(fields),
            COREMapKind_STR2ARG_MAP)
        return Args(gen_args,self)

    def load_from_file(self, file_name):
        err = ct.c_bool(False)
        m = libcoreir_c.CORELoadModule(
                self.context, ct.c_char_p(str.encode(file_name)),ct.byref(err))
        if (err.value):
           self.print_errors()

        return coreir.module.Module(m,self)

    def load_library(self, name):
        lib = load_shared_lib(name)
        func = getattr(lib,"CORELoadLibrary_{}".format(name))
        func.argtypes = [COREContext_p]
        func.restype = CORENamespace_p
        return Namespace(func(self.context), self)

    def get_namespace(self,name):
      ns = libcoreir_c.COREGetNamespace(self.context,ct.c_char_p(str.encode(name)))
      return Namespace(ns,self)

    def __del__(self):
        libcoreir_c.COREDeleteContext(self.context)

    def get_named_type(self, namespace, type_name):
        return Type(
            libcoreir_c.COREContextNamed(self.context, str.encode(namespace), str.encode(type_name)),
            self)
