import coreir
import ctypes as ct
from test_utils import get_pointer_addr


def test_directed_module():
    c = coreir.Context()
    module_typ = c.Record({"input": c.Array(8, c.BitIn()), "output": c.Array(8, c.Bit())})
    module = c.G.new_module("multiply_by_4", module_typ)
    module_def = module.new_definition()
    add8 = c.G.new_module("add8",
        c.Record({
            "in1": c.Array(8, c.BitIn()),
            "in2": c.Array(8, c.BitIn()),
            "out": c.Array(8, c.Bit())
        })
    )
    add8_inst1 = module_def.add_module_instance("adder1", add8)
    add8_inst2 = module_def.add_module_instance("adder2", add8)
    add8_inst3 = module_def.add_module_instance("adder3", add8)
    interface = module_def.interface
    _input = interface.select("input")
    for adder in [add8_inst1, add8_inst2]:
        module_def.connect(_input, adder.select("in1"))
        module_def.connect(_input, adder.select("in2"))
    module_def.connect(add8_inst1.select("out"), add8_inst3.select("in1"))
    module_def.connect(add8_inst2.select("out"), add8_inst3.select("in2"))
    module_def.connect(add8_inst3.select("out"), interface.select("output"))
    module.definition = module_def
    directed_module = module.directed_module
    # check inputs
    expected = [["adder1", "in1"], ["adder1", "in2"], ["adder2", "in1"], ["adder2", "in2"]]
    for input in directed_module.inputs:
        assert input.source == ["self", "input"]
        assert input.sink in expected, "Unexpected sink {}".format(input.sink)
        expected.remove(input.sink)
    assert len(expected) == 0, "Did not find {}".format(expected)

    # check outputs
    expected = [["adder3", "out"]]
    for output in directed_module.outputs:
        assert output.sink == ["self", "output"]
        assert output.source in expected, "Unexpected source {}".format(input.sink)
        expected.remove(output.source)
    assert len(expected) == 0, "Did not find {}".format(expected)

    assert get_pointer_addr(directed_module.sel(["adder3", "out"]).ptr) == get_pointer_addr(add8_inst3.select("out").ptr)

    expected = [
        (['adder3', 'out'], ['self', 'output'], 8),
        (['adder2', 'out'], ['adder3', 'in2'], 8),
        (['adder1', 'out'], ['adder3', 'in1'], 8),
        (['self', 'input'], ['adder1', 'in1'], 8),
        (['self', 'input'], ['adder2', 'in1'], 8),
        (['self', 'input'], ['adder1', 'in2'], 8),
        (['self', 'input'], ['adder2', 'in2'], 8)
    ]
    for directed_connection in directed_module.connections:
        actual = (directed_connection.source, directed_connection.sink, directed_connection.size)
        assert actual in expected
        expected.remove(actual)
    assert len(expected) == 0

    # check instances
    for instance in directed_module.instances:
        for input in instance.inputs:
            assert input.source in [["self", "input"], ["adder1", "out"], ["adder2", "out"]]
            assert input.sink[0] in ["adder1", "adder2", "adder3"]
            assert input.sink[1] in ["in1", "in2"]
        for output in instance.outputs:
            assert output.source[0] in ["adder1", "adder2", "adder3"]
            assert output.source[1] == "out"
            assert output.sink in [["self", "output"], ["adder3", "in1"], ["adder3", "in2"]]


if __name__ == "__main__":
    test_directed_module()
