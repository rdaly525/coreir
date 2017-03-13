import coreir
import ctypes as ct


#def main():
#  test_save_module()

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
    c.load_from_file("python_test_output.json")


def test_module_def_get_instances():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.BitOut())})
    module = c.G.Module("multiply_by_2", module_typ)
    module_def = module.new_definition()
    add8 = c.G.Module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.BitOut())
        })
    )
    add8_inst_1 = module_def.add_instance_module("adder1", add8)
    add8_inst_2 = module_def.add_instance_module("adder2", add8)
    instances = module_def.get_instances()
    pointers_actual = [ct.addressof(inst.ptr.contents) for inst in instances]
    pointers_expected = [ct.addressof(inst.ptr.contents) for inst in [add8_inst_1, add8_inst_2]]
    for pointer in pointers_actual:
        assert pointer in pointers_expected
        pointers_expected.remove(pointer)


def test_module_def_get_connections():
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
    connections = module_def.get_connections()
    for conn in connections:
        print(conn.first, conn.second)

#if __name__ == "__main__":
#  main()

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
