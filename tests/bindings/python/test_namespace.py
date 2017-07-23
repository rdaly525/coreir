import coreir


def test_get_name():
    context = coreir.Context()
    assert context.G.name == "_G"
    stdlib = context.load_library("stdlib")
    assert stdlib.name == "stdlib"
    add_instantiable = stdlib.instantiables["add"]
    assert add_instantiable.name == "add"
    assert add_instantiable.kind == Generator
