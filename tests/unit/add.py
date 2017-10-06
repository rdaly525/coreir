import coreir
import ctypes
from functools import wraps

def type_gen(fn):
    @wraps(fn)
    def wrapped(context, names, values, num_values):
        print("Hello")
        context = coreir.Context(ctypes.cast(context, coreir.COREContext_p))
        values = ctypes.cast(values, ctypes.POINTER(coreir.COREValue_p))
        names = ctypes.cast(names, ctypes.POINTER(ctypes.c_char_p))
        values_map = {}
        for i in range(num_values):
            values_map[names[i]] = coreir.Value(values[i], context)
        return fn(context, values_map)
    return wrapped

@type_gen
def add_type_gen(context, values):
    print({key: value.value for key, value in values.items()})
    print("Success")
