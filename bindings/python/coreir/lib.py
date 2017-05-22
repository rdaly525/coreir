from ctypes import cdll
import platform
import os


def load_shared_lib(suffix):
    _system = platform.system()
    if _system == "Linux":
        shared_lib_ext = "so"
    elif _system == "Darwin":
        shared_lib_ext = "dylib"
    else:
        raise NotImplementedError(_system)

    dir_path = os.path.dirname(os.path.realpath(__file__))

    return cdll.LoadLibrary('{}/../../../lib/libcoreir-{}.{}'.format(dir_path, suffix, shared_lib_ext))

libcoreir_c = load_shared_lib("c")
