import coreir


def test_get_type():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    module_def = module.new_definition()
    wireable = module_def.interface
    assert wireable.type.kind == "Record"
