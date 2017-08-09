import itertools
from collections import namedtuple


class Source:
    def __init__(self):
        self._source = ""

    def add_line(self, text=""):
        self._source += text + "\n"

    def __str__(self):
        return self._source


prim = namedtuple("prim", ["name", "in_types", "return_types"])


UInt = "UInt"
SInt = "SInt"

source = Source()
standard_in_types = tuple(itertools.product((UInt, SInt), (UInt, SInt)))

binary_ops = [
    prim("add",  standard_in_types, (UInt, SInt, SInt, SInt)),
    prim("sub",  standard_in_types, (SInt, SInt, SInt, SInt)),
    prim("mul",  standard_in_types, (UInt, SInt, SInt, SInt)),
    prim("div",  standard_in_types, (UInt, SInt, SInt, SInt)),
    prim("mod",  standard_in_types, (UInt, UInt, SInt, SInt)),
    prim("lt",   standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("leq",  standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("gt",   standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("geq",  standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("eq",   standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("neq",  standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("dshl", ((UInt, UInt), (UInt, SInt)), (UInt, SInt)),
    prim("dshr", ((UInt, UInt), (UInt, SInt)), (UInt, SInt)),
    prim("and",  standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("or",   standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("xor",  standard_in_types, (UInt, UInt, UInt, UInt)),
    prim("cat",  standard_in_types, (UInt, UInt, UInt, UInt)),
]

types = ["UInt", "SInt"]

def get_primitive_arg(name, typ):
    if typ == SInt:
        name = "asSInt({})".format(name)
    return name


for op in binary_ops:
    for (in0_type, in1_type), out_type in zip(op.in_types, op.return_types):
        source.add_line("  module {}_{}_{} :".format(op.name, in0_type, in1_type))
        source.add_line("    input in0  : UInt")
        source.add_line("    input in1  : UInt")
        source.add_line("    output out : UInt")
        source.add_line()
        in0 = get_primitive_arg("in0", in0_type)
        in1 = get_primitive_arg("in1", in1_type)
        result = "{}({}, {})".format(op.name, in0, in1)
        if out_type == SInt:
            result = "asUInt({})".format(result)
        source.add_line("    out <= {}".format(result))
        source.add_line()

unary_ops = [
    prim("cvt", (UInt, SInt), (SInt, SInt)),
    prim("neg", (UInt, SInt), (SInt, SInt)),
    prim("not", (UInt, SInt), (UInt, UInt)),
    prim("andr", (UInt, SInt), (UInt, UInt)),
    prim("orr",  (UInt, SInt), (UInt, UInt)),
    prim("xorr", (UInt, SInt), (UInt, UInt)),
]

for op in unary_ops:
    for in_type, out_type in zip(op.in_types, op.return_types):
        source.add_line("  module {}_{} :".format(op.name, in_type))
        source.add_line("    input in   : UInt")
        source.add_line("    output out : UInt")
        source.add_line()
        _in = get_primitive_arg("in", in_type)
        result = "{}({})".format(op.name, _in)
        if out_type == SInt:
            result = "asUInt({})".format(result)
        source.add_line("    out <= {}".format(result))
        source.add_line()

with open("primitive_wrappers.fir", "w") as output:
    output.write(str(source))

