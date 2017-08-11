  module coreir_not :
    input in   : UInt
    output out : UInt

    assign out <= not(in)

  module coreir_neg :
    input in   : UInt
    output out : UInt

    assign out <= asUInt(neg(in))

  module coreir_andr :
    input in   : UInt
    output out : UInt

    assign out <= andr(in)

  module coreir_orr :
    input in   : UInt
    output out : UInt

    assign out <= orr(in)

  module coreir_xorr :
    input in   : UInt
    output out : UInt

    assign out <= xorr(in)

  module coreir_and :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= and(in0, in1)

  module coreir_or :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= or(in0, in1)

  module coreir_xor :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= xor(in0, in1)

  module coreir_dshl :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= dshl(in0, in1)

  module coreir_dlshr :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= dshr(in0, in1)

  module coreir_dashr :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(dshr(asSInt(in0), in1))

  module coreir_add :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= add(in0, in1)

  module coreir_sub :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= sub(in0, in1)

  module coreir_mul :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= mul(in0, in1)

  module coreir_udiv :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= div(in0, in1)

  module coreir_urem :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= mod(in0, in1)

  module coreir_sdiv :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(div(asSInt(in0), asSInt(in1)))

  module coreir_srem :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(mod(asSInt(in0), asSInt(in1)))

  module coreir_eq :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= eq(in0, in1)

  module coreir_slt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(lt(asSInt(in0),  asSInt(in1)))

  module coreir_sgt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(gt(asSInt(in0),  asSInt(in1)))

  module coreir_sle :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(leq(asSInt(in0), asSInt(in1)))

  module coreir_sge :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= asUInt(gte(asSInt(in0), asSInt(in1)))

  module coreir_ult :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= lt(in0, in1)

  module coreir_ugt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= gt(in0, in1)

  module coreir_ule :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= leq(in0, in1)

  module coreir_uge :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    assign out <= geq(in0, in1)

