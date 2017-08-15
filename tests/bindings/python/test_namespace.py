import coreir
import test_utils


def test_coreir():
    context = coreir.Context()
    assert context.G.name == "_G"
    coreir_stdlib = context.get_namespace("coreir")
    assert coreir_stdlib.name == "coreir"
    add_instantiable = coreir_stdlib.instantiables["add"]
    assert add_instantiable.name == "add"
    assert add_instantiable.kind == coreir.instantiable.Generator

    add_generator = coreir_stdlib.generators["add"]
    assert add_generator.name == "add"
    test_utils.assert_pointers_equal(add_generator.ptr, add_instantiable.ptr)

    module_typ = context.Record({"input": context.Array(8, context.BitIn()), "output": context.Array(9, context.Bit())})
    module = context.G.new_module("multiply_by_2", module_typ)
    module_def = module.new_definition()
    add8_inst = module_def.add_generator_instance("add8_inst", add_generator, context.newArgs({"width":8}))
    assert add8_inst.generator_args["width"].value == 8


def test_ice40():
    context = coreir.Context()
    coreir_ice40 = context.load_library("ice40")
    sb_lut4 = coreir_ice40.modules["SB_LUT4"]
    # assert sb_lut4.name == "SB_LUT4"
    # assert sb_lut4.type.kind == "Record"
