  module add_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= add(in0, in1)

  module add_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(add(in0, asSInt(in1)))

  module add_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(add(asSInt(in0), in1))

  module add_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(add(asSInt(in0), asSInt(in1)))

  module sub_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(sub(in0, in1))

  module sub_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(sub(in0, asSInt(in1)))

  module sub_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(sub(asSInt(in0), in1))

  module sub_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(sub(asSInt(in0), asSInt(in1)))

  module mul_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= mul(in0, in1)

  module mul_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(mul(in0, asSInt(in1)))

  module mul_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(mul(asSInt(in0), in1))

  module mul_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(mul(asSInt(in0), asSInt(in1)))

  module div_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= div(in0, in1)

  module div_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(div(in0, asSInt(in1)))

  module div_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(div(asSInt(in0), in1))

  module div_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(div(asSInt(in0), asSInt(in1)))

  module mod_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= mod(in0, in1)

  module mod_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= mod(in0, asSInt(in1))

  module mod_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(mod(asSInt(in0), in1))

  module mod_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(mod(asSInt(in0), asSInt(in1)))

  module lt_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= lt(in0, in1)

  module lt_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= lt(in0, asSInt(in1))

  module lt_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= lt(asSInt(in0), in1)

  module lt_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= lt(asSInt(in0), asSInt(in1))

  module leq_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= leq(in0, in1)

  module leq_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= leq(in0, asSInt(in1))

  module leq_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= leq(asSInt(in0), in1)

  module leq_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= leq(asSInt(in0), asSInt(in1))

  module gt_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= gt(in0, in1)

  module gt_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= gt(in0, asSInt(in1))

  module gt_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= gt(asSInt(in0), in1)

  module gt_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= gt(asSInt(in0), asSInt(in1))

  module geq_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= geq(in0, in1)

  module geq_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= geq(in0, asSInt(in1))

  module geq_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= geq(asSInt(in0), in1)

  module geq_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= geq(asSInt(in0), asSInt(in1))

  module eq_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= eq(in0, in1)

  module eq_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= eq(in0, asSInt(in1))

  module eq_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= eq(asSInt(in0), in1)

  module eq_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= eq(asSInt(in0), asSInt(in1))

  module neq_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= neq(in0, in1)

  module neq_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= neq(in0, asSInt(in1))

  module neq_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= neq(asSInt(in0), in1)

  module neq_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= neq(asSInt(in0), asSInt(in1))

  module dshl_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= dshl(in0, in1)

  module dshl_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(dshl(in0, asSInt(in1)))

  module dshr_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= dshr(in0, in1)

  module dshr_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= asUInt(dshr(in0, asSInt(in1)))

  module and_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= and(in0, in1)

  module and_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= and(in0, asSInt(in1))

  module and_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= and(asSInt(in0), in1)

  module and_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= and(asSInt(in0), asSInt(in1))

  module or_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= or(in0, in1)

  module or_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= or(in0, asSInt(in1))

  module or_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= or(asSInt(in0), in1)

  module or_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= or(asSInt(in0), asSInt(in1))

  module xor_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= xor(in0, in1)

  module xor_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= xor(in0, asSInt(in1))

  module xor_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= xor(asSInt(in0), in1)

  module xor_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= xor(asSInt(in0), asSInt(in1))

  module cat_UInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= cat(in0, in1)

  module cat_UInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= cat(in0, asSInt(in1))

  module cat_SInt_UInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= cat(asSInt(in0), in1)

  module cat_SInt_SInt :
    input in0  : UInt
    input in1  : UInt
    output out : UInt

    out <= cat(asSInt(in0), asSInt(in1))

  module cvt_UInt :
    input in   : UInt
    output out : UInt

    out <= asUInt(cvt(in))

  module cvt_SInt :
    input in   : UInt
    output out : UInt

    out <= asUInt(cvt(asSInt(in)))

  module neg_UInt :
    input in   : UInt
    output out : UInt

    out <= asUInt(neg(in))

  module neg_SInt :
    input in   : UInt
    output out : UInt

    out <= asUInt(neg(asSInt(in)))

  module not_UInt :
    input in   : UInt
    output out : UInt

    out <= not(in)

  module not_SInt :
    input in   : UInt
    output out : UInt

    out <= not(asSInt(in))

  module andr_UInt :
    input in   : UInt
    output out : UInt

    out <= andr(in)

  module andr_SInt :
    input in   : UInt
    output out : UInt

    out <= andr(asSInt(in))

  module orr_UInt :
    input in   : UInt
    output out : UInt

    out <= orr(in)

  module orr_SInt :
    input in   : UInt
    output out : UInt

    out <= orr(asSInt(in))

  module xorr_UInt :
    input in   : UInt
    output out : UInt

    out <= xorr(in)

  module xorr_SInt :
    input in   : UInt
    output out : UInt

    out <= xorr(asSInt(in))

