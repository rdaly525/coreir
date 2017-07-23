import coreir
import test_utils


def test_get_name():
    context = coreir.Context()
    assert context.G.name == "_G"
    stdlib = context.load_library("stdlib")
    assert stdlib.name == "stdlib"
    add_instantiable = stdlib.instantiables["add"]
    assert add_instantiable.name == "add"
    assert add_instantiable.kind == coreir.instantiable.Generator

    add_generator = stdlib.generators["add"]
    assert add_generator.name == "add"
    test_utils.assert_pointers_equal(add_generator.ptr, add_instantiable.ptr)
