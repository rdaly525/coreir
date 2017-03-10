import coreir

def test_save_module():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.BitOut())})
    module = c.G.Module("multiply_by_2", module_typ)
    # module.print()
    module_def = module.new_definition()
    add8 = c.G.Module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.BitOut())
        })
    )
    add8_inst = module_def.add_instance_module("adder", add8)
    add8_in1 = add8_inst.select("in1")
    add8_in2 = add8_inst.select("in2")
    add8_out = add8_inst.select("out")
    interface = module_def.get_interface()
    _input = interface.select("input")
    output = interface.select("output")
    module_def.wire(_input, add8_in1)
    module_def.wire(_input, add8_in2)
    module_def.wire(output, add8_out)
    module.add_definition(module_def)
    module.save_to_file("python_test_output.json")

# def test():
#     c = coreir.Context()
#     # any = c.Any()
#     # any.print()
#     # c.BitIn().print()
#     # c.BitOut().print()
#     # c.Array(3, c.BitIn()).print()
# 
#     # c.Array(3, c.Array(4, c.BitIn())).print()
# 
#     # c.ModuleFromFile("test").print()
#     module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.BitOut())})
#     module = c.G.Module("multiply_by_2", module_typ)
#     module.print()
#     module_def = module.new_definition()
#     add8 = c.G.Module("add8",
#         c.Record({
#             "in1": c.Array(8, c.BitIn()),
#             "in2": c.Array(8, c.BitIn()),
#             "out": c.Array(9, c.BitOut())
#         })
#     )
#     add8_inst = module_def.add_instance_module("adder", add8)
#     add8_in1 = add8_inst.select("in1")
#     add8_in2 = add8_inst.select("in2")
#     add8_out = add8_inst.select("out")
#     interface = module_def.get_interface()
#     _input = interface.select("input")
#     output = interface.select("output")
#     module_def.wire(_input, add8_in1)
#     module_def.wire(_input, add8_in2)
#     module_def.wire(output, add8_out)
#     module.add_definition(module_def)
#     module.print()
