class Source:
    def __init__(self):
        self._source = ""

    def add_line(self, text=""):
        self._source += text + "\n"

    def __str__(self):
        return self._source


source = Source()

ops = {
    "unary": {
        "not" : "not(in)",
        "neg" : "neg(in)",
        "andr" : "andr(in)",
        "orr"  : "orr(in)",
        "xorr" : "xorr(in)"
    },
    "binary": {
        "and"   : "and(in0, in1)",
        "or"    : "or(in0, in1)",
        "xor"   : "xor(in0, in1)",
        "dshl"  : "dshl(in0, in1)",
        "dlshr" : "dshr(in0, in1)",
        "dashr" : "dshr(asSInt(in0), in1)",
        "add"   : "add(in0, in1)",
        "sub"   : "sub(in0, in1)",
        "mul"   : "mul(in0, in1)",
        "udiv"  : "div(in0, in1)",
        "urem"  : "mod(in0, in1)",
        "sdiv"  : "div(asSInt(in0), asSInt(in1))",
        "srem"  : "mod(asSInt(in0), asSInt(in1))", 
        # "smod"  : "$signed(in0) % $signed(in1)", #TODO definitely wrong
        "eq"  : "eq(in0, in1)",
        "slt" : "lt(asSInt(in0),  asSInt(in1))",
        "sgt" : "gt(asSInt(in0),  asSInt(in1))",
        "sle" : "leq(asSInt(in0), asSInt(in1))",
        "sge" : "gte(asSInt(in0), asSInt(in1))",
        "ult" : "lt(in0, in1)",
        "ugt" : "gt(in0, in1)",
        "ule" : "leq(in0, in1)",
        "uge" : "geq(in0, in1)"
    }
    # "static_shift": {
    #     "lshr" : "in >> SHIFTBITS",
    #     "shl"  : "in << SHIFTBITS",
    #     "ashr" : "$signed(in) >>> SHIFTBITS"
    # },
}

source = Source()

for _type, ops_set in ops.items():
    for op, body in ops_set.items():
        source.add_line(    "  module coreir_{} :".format(op))
        if _type == "unary":
            source.add_line("    input in   : UInt")
            source.add_line("    output out : UInt")
            source.add_line()
        if _type == "binary":
            source.add_line("    input in0  : UInt")
            source.add_line("    input in1  : UInt")
            source.add_line("    output out : UInt")
            source.add_line()
        source.add_line(    "    assign out <= {}".format(body))
        source.add_line()


with open("primitive_wrappers.fir", "w") as output:
    output.write(str(source))

