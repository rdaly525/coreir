import magma as m
import mantle


class TestNestedClockTuple(m.Circuit):
    io = m.IO(I=m.In(m.Tuple(clk1=m.Clock, clk2=m.Clock, i=m.Bit)),
          O=m.Out(m.Bits(2)))

    @classmethod
    def definition(io):
        ff0 = mantle.FF()
        ff1 = mantle.FF()
        m.wire(io.I.clk1, ff0.CLK)
        m.wire(io.I.clk2, ff1.CLK)
        m.wire(io.I.i, ff0.I)
        m.wire(io.I.i, ff1.I)
        m.wire(m.bits([ff0.O, ff1.O]), io.O)


class TestNestedClockTupleMain(m.Circuit):
    io = m.IO(CLK=m.In(m.Clock), I=m.In(m.Bit), O=m.Out(m.Bits(2)))

    @classmethod
    def definition(io):
        # Coreir should automatically wire io.CLK to circ.
        circ = TestNestedClockTuple()
        m.wire(circ.I.i, io.I)
        m.wire(circ.O, io.O)


print(repr(TestNestedClockTuple))
m.compile("TestNestedClockTuple", TestNestedClockTupleMain, output="coreir")
