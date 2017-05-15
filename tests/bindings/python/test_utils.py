import ctypes as ct

def get_pointer_addr(ptr):
    return ct.cast(ptr, ct.c_void_p).value

def assert_pointers_equal(ptr1, ptr2):
    assert get_pointer_addr(ptr1) == get_pointer_addr(ptr2)
