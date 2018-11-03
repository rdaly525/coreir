# Use this to generate the input .json files and output golds
import magma as m
from magma.testing.utils import check_files_equal
import mantle
import fault
import fault.random
import os


def test_simple_top():
    Top = m.DefineCircuit("Top", "I0", m.In(m.UInt(8)), "I1", m.In(m.UInt(8)), "O", m.Out(m.UInt(8)))
    sum_ = Top.I0 + Top.I1
    m.wire(sum_, Top.O)
    m.EndCircuit()

    m.compile("test_simple_top", Top, output="coreir-verilog", inline=True)
    # assert check_files_equal(__file__, "build/test_simple_top.v",
    #                          "gold/test_simple_top.v")


def test_two_ops():
    Top = m.DefineCircuit("test_two_ops", "I0", m.In(m.UInt(8)), "I1", m.In(m.UInt(8)), "O", m.Out(m.UInt(8)))
    result = Top.I0 + Top.I1 - Top.I0
    m.wire(result, Top.O)
    m.EndCircuit()

    m.compile("test_two_ops", Top, output="coreir-verilog", inline=True)
    # assert check_files_equal(__file__, "build/test_two_ops.v",
    #                          "gold/test_two_ops.v")
    # Roundabout way to do this since we can't pass the --inline flag through
    # fault's tester interface yet

    tester = fault.Tester(Top)

    for i in range(0, 16):
        I0 = fault.random.random_bv(8)
        I1 = fault.random.random_bv(8)
        tester.poke(Top.I0, I0)
        tester.poke(Top.I1, I1)
        tester.eval()
        tester.expect(Top.O, I0 + I1 - I0)

    tester.compile_and_run(target="verilator",
                           skip_compile=True,
                           directory=".")


def test_const():
    Top = m.DefineCircuit("test_const", "I0", m.In(m.UInt(8)), "I1", m.In(m.UInt(8)), "O", m.Out(m.UInt(8)))
    result = Top.I0 + Top.I1 * m.uint(3, 8)
    m.wire(result, Top.O)
    m.EndCircuit()

    m.compile("test_const", Top, output="coreir-verilog", inline=True)

    tester = fault.Tester(Top)

    for i in range(0, 16):
        I0 = fault.random.random_bv(8)
        I1 = fault.random.random_bv(8)
        tester.poke(Top.I0, I0)
        tester.poke(Top.I1, I1)
        tester.eval()
        tester.expect(Top.O, I0 + I1 * 3)

    tester.compile_and_run(target="verilator",
                           skip_compile=True,
                           directory=".")
