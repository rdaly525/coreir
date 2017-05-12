import coreir
import ctypes as ct

def get_pointer_addr(ptr):
    return ct.cast(ptr, ct.c_void_p).value

def assert_pointers_equal(ptr1, ptr2):
    assert get_pointer_addr(ptr1) == get_pointer_addr(ptr2)


def test_load_library():
    c = coreir.Context()
    stdlib = c.load_library("stdlib")
    assert stdlib.name == "stdlib"

def test_save_module():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    module.print_()
    module_def = module.new_definition()
    configparams = c.newParams({"init":c.AINT}) 
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        }),
        configparams
    )
    add8_inst = module_def.add_module_instance("adder", add8,c.newArgs({"init":5}))
    print(add8_inst.module_name())
    print(add8_inst.get_config_value("init"))
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
    module.print_()
    module.save_to_file("python_test_output.json")
    mod = c.load_from_file("python_test_output.json")
    mod_def = mod.get_definition()
    print("=====================")
    mod_def.print_()
    module_def.print_()
    print("=====================")


def test_module_def_get_instances():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        })
    )
    add8_inst_1 = module_def.add_module_instance("adder1", add8)
    add8_inst_2 = module_def.add_module_instance("adder2", add8)
    instances = module_def.get_instances()
    pointers_actual = [get_pointer_addr(inst.ptr) for inst in instances]
    pointers_expected = [get_pointer_addr(inst.ptr) for inst in [add8_inst_1, add8_inst_2]]
    for pointer in pointers_actual:
        assert pointer in pointers_expected
        pointers_expected.remove(pointer)

    assert_pointers_equal(instances[0].get_module_def().ptr, module_def.ptr)
    assert_pointers_equal(instances[0].get_module().ptr, module.ptr)

def test_module_def_select():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    # module.print()
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        })
    )
    interface = module_def.get_interface()
    assert get_pointer_addr(interface.ptr) == get_pointer_addr(module_def.select("self").ptr)
    add8_inst = module_def.add_module_instance("adder", add8)
    add8_inst_select = module_def.select("adder")
    assert get_pointer_addr(add8_inst.ptr) == get_pointer_addr(add8_inst_select.ptr)

def test_wireable():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    # module.print()
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        })
    )
    add8_inst = module_def.add_module_instance("adder", add8)
    add8_in1 = add8_inst.select("in1")
    add8_in2 = add8_inst.select("in2")
    add8_out = add8_inst.select("out")
    interface = module_def.get_interface()
    _input = interface.select("input")
    output = interface.select("output")
    module_def.wire(_input, add8_in1)
    module_def.wire(_input, add8_in2)
    module_def.wire(output, add8_out)
    actual = [get_pointer_addr(wireable.ptr) for wireable in _input.get_connected_wireables()]
    assert get_pointer_addr(add8_in1.ptr) in actual
    assert get_pointer_addr(add8_in2.ptr) in actual
    for expected, actual in zip(['adder', 'out'], add8_out.get_selectpath()):
        assert expected == actual

    wireable = module_def.select("self")
    assert get_pointer_addr(wireable.select("input").ptr) == get_pointer_addr(_input.ptr)

def test_module_def_get_connections():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_2", module_typ)
    # module.print()
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        })
    )
    add8_inst = module_def.add_module_instance("adder", add8)
    add8_in1 = add8_inst.select("in1")
    add8_in2 = add8_inst.select("in2")
    add8_out = add8_inst.select("out")
    interface = module_def.get_interface()
    _input = interface.select("input")
    output = interface.select("output")
    module_def.wire(_input, add8_in1)
    module_def.wire(_input, add8_in2)
    module_def.wire(output, add8_out)
    input_ptr = get_pointer_addr(_input.ptr)
    add8_in1_ptr = get_pointer_addr(add8_in1.ptr)
    add8_in2_ptr = get_pointer_addr(add8_in2.ptr)
    add8_out_ptr = get_pointer_addr(add8_out.ptr)
    output_ptr = get_pointer_addr(output.ptr)
    expected_conns = [
        (add8_in1_ptr, input_ptr),
        (add8_in2_ptr, input_ptr),
        (add8_out_ptr, output_ptr)
    ]
    connections = module_def.get_connections()
    seen = []
    for conn in connections:
        pair = (get_pointer_addr(conn.first.ptr), get_pointer_addr(conn.second.ptr))
        reverse_pair = (pair[1], pair[0])
        # Should be in expected, shouldn't see it twice
        assert (pair in expected_conns or reverse_pair in expected_conns) and \
               pair not in seen
        seen.append(pair)
    assert len(seen) == len(expected_conns)

def test_directed_module():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
    module = c.G.new_module("multiply_by_4", module_typ)
    # module.print()
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(9, c.Bit())
        })
    )
    add8_inst1 = module_def.add_module_instance("adder1", add8)
    add8_inst2 = module_def.add_module_instance("adder2", add8)
    add8_inst3 = module_def.add_module_instance("adder3", add8)
    interface = module_def.get_interface()
    _input = interface.select("input")
    for adder in [add8_inst1, add8_inst2]:
        module_def.wire(_input, adder.select("in1"))
        module_def.wire(_input, adder.select("in2"))
    module_def.wire(add8_inst1.select("out"), add8_inst3.select("in1"))
    module_def.wire(add8_inst2.select("out"), add8_inst3.select("in2"))
    module_def.wire(add8_inst3.select("out"), interface.select("output"))
    module.add_definition(module_def)
    directed_module = module.new_directed_view()

    # check inputs
    expected = [["adder1", "in1"], ["adder1", "in2"], ["adder2", "in1"], ["adder2", "in2"]]
    for input in directed_module.get_inputs():
        assert input.source == ["self", "input"]
        assert input.sink in expected, "Unexpected sink {}".format(input.sink)
        expected.remove(input.sink)
    assert len(expected) == 0, "Did not find {}".format(expected)

    # check outputs
    expected = [["adder3", "out"]]
    for output in directed_module.get_outputs():
        assert output.sink == ["self", "output"]
        assert output.source in expected, "Unexpected source {}".format(input.sink)
        expected.remove(output.source)
    assert len(expected) == 0, "Did not find {}".format(expected)

    assert get_pointer_addr(directed_module.sel(["adder3", "out"]).ptr) == get_pointer_addr(add8_inst3.select("out").ptr)


if __name__ == "__main__":
    test_directed_module()
# def test():
#     c = coreir.Context()
#     # any = c.Any()
#     # any.print()
#     # c.BitIn().print()
#     # c.Bit().print()
#     # c.Array(3, c.BitIn()).print()
# 
#     # c.Array(3, c.Array(4, c.BitIn())).print()
# 
#     # c.ModuleFromFile("test").print()
#     module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(9, c.Bit())})
#     module = c.G.new_module("multiply_by_2", module_typ)
#     module.print()
#     module_def = module.new_definition()
#     add8 = c.G.new_module("add8",
#         c.Record({
#             "in1": c.Array(8, c.BitIn()),
#             "in2": c.Array(8, c.BitIn()),
#             "out": c.Array(9, c.Bit())
#         })
#     )
#     add8_inst = module_def.add_module_instance("adder", add8)
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
