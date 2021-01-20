#ifndef COREIR_BSIM_TEXT_HPP
#define COREIR_BSIM_TEXT_HPP

#include <string>

using namespace std;

namespace CoreIR {

static string blib() {
  return string(
    "#pragma once\n"
    "\n"
    "#include <bitset>\n"
    "#include <cassert>\n"
    "#include <iostream>\n"
    "#include <stdint.h>\n"
    "#include <type_traits>\n"
    "\n"
    "#define GEN_NUM_BYTES(N) (((N) / 8) + 1 - (((N) % 8 == 0)))\n"
    "#define NUM_BYTES_GT_8(N) GEN_NUM_BYTES(N)\n"
    "#define NUM_BYTES_GT_4(N) (N <= 64 ? 8 : NUM_BYTES_GT_8(N))\n"
    "#define NUM_BYTES_GT_2(N) (N <= 32 ? 4 : NUM_BYTES_GT_4(N))\n"
    "#define NUM_BYTES_GT_1(N) (N <= 16 ? 2 : NUM_BYTES_GT_2(N))\n"
    "#define NUM_BYTES(N) (N <= 8 ? (1) : NUM_BYTES_GT_1(N))\n"
    "\n"
    "typedef int8_t  bv_sint8;\n"
    "typedef int32_t  bv_sint32;\n"
    "\n"
    "typedef uint8_t  bv_uint8;\n"
    "typedef uint16_t bv_uint16;\n"
    "typedef uint32_t bv_uint32;\n"
    "typedef uint64_t bv_uint64;\n"
    "\n"
    "namespace bsim {\n"
    "\n"
    "  template<int N>\n"
    "  class bit_vector {\n"
    "    unsigned char bits[NUM_BYTES(N)];\n"
    "\n"
    "  public:\n"
    "    bit_vector() {\n"
    "      for (int i = 0; i < N; i++) {\n"
    "	set(i, 0);\n"
    "      }\n"
    "    }\n"
    "\n"
    "    bit_vector(const std::string& str) {\n"
    "      assert(str.size() == N);\n"
    "\n"
    "      for (int i = N - 1; i >= 0; i--) {\n"
    "	unsigned char val = (str[i] == '0') ? 0 : 1;\n"
    "	int ind = N - i - 1;\n"
    "	set(ind, val);\n"
    "      }\n"
    "    }\n"
    "\n"
    "    bit_vector(const int val) {\n"
    "      *((int*) (&bits)) = val;\n"
    "    }\n"
    "\n"
    "    bit_vector(const bv_uint64 val) {\n"
    "      *((bv_uint64*)(&bits)) = val;\n"
    "    }\n"
    "    \n"
    "    bit_vector(const bv_uint32 val) {\n"
    "      *((bv_uint32*)(&bits)) = val;\n"
    "    }\n"
    "\n"
    "    bit_vector(const bv_uint16 val) {\n"
    "      *((bv_uint16*)(&bits)) = val;\n"
    "    }\n"
    "\n"
    "    bit_vector(const bv_uint8 val) {\n"
    "      *((bv_uint8*)(&bits)) = val;\n"
    "    }\n"
    "    \n"
    "    bit_vector(const bit_vector<N>& other) {\n"
    "      for (int i = 0; i < NUM_BYTES(N); i++) {\n"
    "	bits[i] = other.bits[i];\n"
    "      }\n"
    "    }\n"
    "\n"
    "    bit_vector<N>& operator=(const bit_vector<N>& other) {\n"
    "      if (&other == this) {\n"
    "    	return *this;\n"
    "      }\n"
    "\n"
    "      for (int i = 0; i < N; i++) {\n"
    "    	set(i, other.get(i));\n"
    "      }\n"
    "\n"
    "      return *this;\n"
    "    }\n"
    "\n"
    "    inline void set(const int ind, const unsigned char val) {\n"
    "      int byte_num = ind / 8;\n"
    "      int bit_num = ind % 8;\n"
    "\n"
    "      unsigned char old = bits[byte_num];\n"
    "      // The & 0x01 only seems to be needed for logical not\n"
    "      old ^= (-(val & 0x01) ^ old) & (1 << bit_num);\n"
    "\n"
    "      bits[byte_num] = old;\n"
    "    }\n"
    "\n"
    "    unsigned char get(const int ind) const {\n"
    "      int byte_num = ind / 8;\n"
    "      int bit_num = ind % 8;\n"
    "\n"
    "      unsigned char target_byte = bits[byte_num];\n"
    "      return 0x01 & (target_byte >> bit_num);\n"
    "    }\n"
    "\n"
    "    inline bool equals(const bit_vector<N>& other) const {\n"
    "\n"
    "      for (int i = 0; i < N; i++) {\n"
    "	if (get(i) != other.get(i)) {\n"
    "	  return false;\n"
    "	}\n"
    "      }\n"
    "\n"
    "      return true;\n"
    "    }\n"
    "\n"
    "    template<typename ConvType>\n"
    "    ConvType to_type() const {\n"
    "      return *((ConvType*) (&bits));\n"
    "    }\n"
    "\n"
    "    inline bv_uint64 as_native_int32() const {\n"
    "      return *((bv_sint32*) (&bits));\n"
    "    }\n"
    "    \n"
    "    inline bv_uint64 as_native_uint64() const {\n"
    "      return *((bv_uint64*) (&bits));\n"
    "    }\n"
    "\n"
    "    inline bv_uint32 as_native_uint32() const {\n"
    "      return *((bv_uint32*) (&bits));\n"
    "    }\n"
    "\n"
    "    inline bv_uint16 as_native_uint16() const {\n"
    "      return *((bv_uint16*) (&bits));\n"
    "    }\n"
    "\n"
    "    inline bv_uint8 as_native_uint8() const {\n"
    "      return *((bv_uint8*) (&bits));\n"
    "    }\n"
    "    \n"
    "  };\n"
    "\n"
    "  template<int N>\n"
    "  static inline std::ostream& operator<<(std::ostream& out, const "
    "bit_vector<N>& a) {\n"
    "    for (int i = N - 1; i >= 0; i--) {\n"
    "      if (a.get(i) == 0) {\n"
    "	out << \"0\";\n"
    "      } else if (a.get(i) == 1) {\n"
    "	out << \"1\";\n"
    "      } else {\n"
    "	assert(false);\n"
    "      }\n"
    "    }\n"
    "\n"
    "    return out;\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator==(const bit_vector<N>& a,\n"
    "				const bit_vector<N>& b) {\n"
    "    return a.equals(b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  class unsigned_int {\n"
    "  protected:\n"
    "    bit_vector<N> bits;\n"
    "\n"
    "  public:\n"
    "    unsigned_int() {}\n"
    "\n"
    "    unsigned_int(const std::string& bitstr) : bits(bitstr){}\n"
    "\n"
    "    unsigned_int(const bit_vector<N>& bits_) : bits(bits_) {}\n"
    "\n"
    "    unsigned_int(const bv_uint8 val) : bits(val) {}\n"
    "    unsigned_int(const bv_uint16 val) : bits(val) {}\n"
    "    unsigned_int(const bv_uint32 val) : bits(val) {}\n"
    "    unsigned_int(const bv_uint64 val) : bits(val) {}\n"
    "\n"
    "    void set(const int ind, const unsigned char val) {\n"
    "      bits.set(ind, val);\n"
    "    }\n"
    "\n"
    "    bit_vector<N> get_bits() const { return bits; }    \n"
    "\n"
    "    unsigned char get(const int ind) const { return bits.get(ind); }\n"
    "\n"
    "    inline bool equals(const unsigned_int<N>& other) const {\n"
    "      return (this->bits).equals((other.bits));\n"
    "    }\n"
    "\n"
    "    inline bv_uint64 as_native_uint64() const {\n"
    "      return bits.as_native_uint64();\n"
    "    }\n"
    "    \n"
    "    inline bv_uint32 as_native_uint32() const {\n"
    "      return bits.as_native_uint32();\n"
    "    }\n"
    "\n"
    "    inline bv_uint16 as_native_uint16() const {\n"
    "      return bits.as_native_uint16();\n"
    "    }\n"
    "\n"
    "    inline bv_uint8 as_native_uint8() const {\n"
    "      return bits.as_native_uint8();\n"
    "    }\n"
    "    \n"
    "    inline std::ostream& print(std::ostream& out) const {\n"
    "      out << bits << \"U\";\n"
    "      return out;\n"
    "    }\n"
    "    \n"
    "  };\n"
    "\n"
    "  template<int N>\n"
    "  class signed_int {\n"
    "  protected:\n"
    "    bit_vector<N> bits;\n"
    "\n"
    "  public:\n"
    "    signed_int() {}\n"
    "\n"
    "\n"
    "    signed_int(const bit_vector<N>& bits_) : bits(bits_) {}\n"
    "\n"
    "    signed_int(const int val) : bits(val) {}\n"
    "\n"
    "    signed_int(const std::string& bitstr) : bits(bitstr) {}\n"
    "\n"
    "    signed_int(const bv_uint8 val) : bits(val) {}\n"
    "    signed_int(const bv_uint16 val) : bits(val) {}\n"
    "    signed_int(const bv_uint32 val) : bits(val) {}\n"
    "    signed_int(const bv_uint64 val) : bits(val) {}\n"
    "\n"
    "    void set(const int ind, const unsigned char val) {\n"
    "      bits.set(ind, val);\n"
    "    }\n"
    "\n"
    "    bit_vector<N> get_bits() const { return bits; }\n"
    "\n"
    "    unsigned char get(const int ind) const { return bits.get(ind); }\n"
    "\n"
    "    inline bool equals(const signed_int<N>& other) const {\n"
    "      return (this->bits).equals((other.bits));\n"
    "    }\n"
    "\n"
    "    template<int HighWidth>\n"
    "    signed_int<HighWidth> sign_extend() const {\n"
    "      signed_int<HighWidth> hw;\n"
    "\n"
    "      for (int i = 0; i < N; i++) {\n"
    "	hw.set(i, get(i));\n"
    "      }\n"
    "    \n"
    "      if (get(N - 1) == 0) {\n"
    "      \n"
    "	return hw;\n"
    "      }\n"
    "\n"
    "      for (int i = N; i < HighWidth; i++) {\n"
    "	hw.set(i, 1);\n"
    "      }\n"
    "\n"
    "      return hw;\n"
    "    }\n"
    "    \n"
    "    bv_sint32 as_native_int32() const {\n"
    "      if (N < 32) {\n"
    "	signed_int<32> extended = sign_extend<32>();\n"
    "\n"
    "	bit_vector<32> bv = extended.get_bits();\n"
    "\n"
    "	return bv.as_native_int32();\n"
    "      }\n"
    "\n"
    "      if (N == 32) {\n"
    "	return get_bits().as_native_int32();\n"
    "      }\n"
    "\n"
    "      assert(false);\n"
    "    }\n"
    "\n"
    "    template<typename ConvType>\n"
    "    ConvType to_type() const {\n"
    "      return bits.template to_type<ConvType>();\n"
    "    }\n"
    "    \n"
    "    inline bv_uint64 as_native_uint64() const {\n"
    "      return bits.as_native_uint64();\n"
    "    }\n"
    "    \n"
    "    inline bv_uint32 as_native_uint32() const {\n"
    "      return bits.as_native_uint32();\n"
    "    }\n"
    "\n"
    "    inline bv_uint16 as_native_uint16() const {\n"
    "      return bits.as_native_uint16();\n"
    "    }\n"
    "\n"
    "    inline bv_uint8 as_native_uint8() const {\n"
    "      return bits.as_native_uint8();\n"
    "    }\n"
    "    \n"
    "    inline std::ostream& print(std::ostream& out) const {\n"
    "      out << bits << \"S\";\n"
    "      return out;\n"
    "    }\n"
    "    \n"
    "  };\n"
    "\n"
    "  template<int Width>\n"
    "  static inline\n"
    "  bit_vector<Width>\n"
    "  add_general_width_bv(const bit_vector<Width>& a,\n"
    "		       const bit_vector<Width>& b) {\n"
    "\n"
    "    bit_vector<Width> res;\n"
    "    unsigned char carry = 0;\n"
    "    for (int i = 0; i < Width; i++) {\n"
    "      unsigned char sum = a.get(i) + b.get(i) + carry;\n"
    "\n"
    "      carry = 0;\n"
    "\n"
    "      unsigned char z_i = sum & 0x01; //sum % 2;\n"
    "      res.set(i, z_i);\n"
    "      if (sum >= 2) {\n"
    "	carry = 1;\n"
    "      }\n"
    "\n"
    "    }\n"
    "\n"
    "    return res;\n"
    "  }\n"
    "\n"
    "  template<int Width>  \n"
    "  static inline\n"
    "  bit_vector<Width>\n"
    "  mul_general_width_bv(const bit_vector<Width>& a,\n"
    "		       const bit_vector<Width>& b) {\n"
    "    bit_vector<2*Width> full_len;\n"
    "\n"
    "    for (int i = 0; i < Width; i++) {\n"
    "      if (b.get(i) == 1) {\n"
    "\n"
    "	bit_vector<2*Width> shifted_a;\n"
    "\n"
    "	for (int j = 0; j < Width; j++) {\n"
    "	  shifted_a.set(j + i, a.get(j));\n"
    "	}\n"
    "\n"
    "	full_len =\n"
    "	  add_general_width_bv(full_len, shifted_a);\n"
    "      }\n"
    "    }\n"
    "\n"
    "    bit_vector<Width> res;\n"
    "    for (int i = 0; i < Width; i++) {\n"
    "      res.set(i, full_len.get(i));\n"
    "    }\n"
    "    return res;\n"
    "  }    \n"
    "\n"
    "  template<int Width>\n"
    "  static inline\n"
    "  bit_vector<Width>\n"
    "  sub_general_width_bv(const bit_vector<Width>& a,\n"
    "		       const bit_vector<Width>& b) {\n"
    "    bit_vector<Width> diff;\n"
    "    bit_vector<Width> a_cpy = a;\n"
    "\n"
    "    bool underflow = false;\n"
    "    for (int i = 0; i < Width; i++) {\n"
    "\n"
    "      if ((a_cpy.get(i) == 0) &&\n"
    "	  (b.get(i) == 1)) {\n"
    "\n"
    "	int j = i + 1;\n"
    "\n"
    "	diff.set(i, 1);	  \n"
    "\n"
    "	// Modify to carry\n"
    "	while ((j < Width) && (a_cpy.get(j) != 1)) {\n"
    "	  a_cpy.set(j, 1);\n"
    "	  j++;\n"
    "	}\n"
    "\n"
    "	if (j >= Width) {\n"
    "	  underflow = true;\n"
    "	} else {\n"
    "	  a_cpy.set(j, 0);\n"
    "	}\n"
    "\n"
    "      } else if (a_cpy.get(i) == b.get(i)) {\n"
    "	diff.set(i, 0);\n"
    "      } else if ((a_cpy.get(i) == 1) &&\n"
    "		 (b.get(i) == 0)) {\n"
    "	diff.set(i, 1);\n"
    "      } else {\n"
    "	assert(false);\n"
    "      }\n"
    "    }\n"
    "\n"
    "    return diff;\n"
    "  }    \n"
    "  \n"
    "  template<int Width>\n"
    "  class signed_int_operations {\n"
    "  public:\n"
    "\n"
    "    static inline\n"
    "    signed_int<Width>\n"
    "    add_general_width(const signed_int<Width>& a,\n"
    "		      const signed_int<Width>& b) {\n"
    "\n"
    "      bit_vector<Width> bits =\n"
    "	add_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      signed_int<Width> c(bits);\n"
    "      return c;\n"
    "    }\n"
    "\n"
    "    static inline\n"
    "    signed_int<Width>\n"
    "    mul_general_width(const signed_int<Width>& a,\n"
    "		      const signed_int<Width>& b) {\n"
    "\n"
    "      bit_vector<Width> bits =\n"
    "	mul_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      signed_int<Width> c(bits);\n"
    "      return c;\n"
    "    }\n"
    "\n"
    "    static inline\n"
    "    signed_int<Width>\n"
    "    sub_general_width(const signed_int<Width>& a,\n"
    "		      const signed_int<Width>& b) {\n"
    "\n"
    "      bit_vector<Width> bits =\n"
    "	sub_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      signed_int<Width> c(bits);\n"
    "      return c;\n"
    "    }\n"
    "    \n"
    "  };  \n"
    "\n"
    "  template<int Width>\n"
    "  class unsigned_int_operations {\n"
    "  public:\n"
    "\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<Q >= 65, unsigned_int<Q> >::type\n"
    "    sub(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "      return sub_general_width(a, b);\n"
    "    }\n"
    "\n"
    "    static inline\n"
    "    unsigned_int<Width>\n"
    "    mul_general_width(const unsigned_int<Width>& a,\n"
    "		      const unsigned_int<Width>& b) {\n"
    "      bit_vector<Width> bits =\n"
    "	mul_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      unsigned_int<Width> c(bits);\n"
    "      return c;\n"
    "\n"
    "    }    \n"
    "\n"
    "    static inline\n"
    "    unsigned_int<Width>\n"
    "    sub_general_width(const unsigned_int<Width>& a,\n"
    "		      const unsigned_int<Width>& b) {\n"
    "      bit_vector<Width> bits =\n"
    "	sub_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      unsigned_int<Width> c(bits);\n"
    "      return c;\n"
    "\n"
    "    }    \n"
    "    \n"
    "    static inline\n"
    "    unsigned_int<Width>\n"
    "    add_general_width(const unsigned_int<Width>& a,\n"
    "		      const unsigned_int<Width>& b) {\n"
    "\n"
    "      bit_vector<Width> bits =\n"
    "	add_general_width_bv(a.get_bits(), b.get_bits());\n"
    "\n"
    "      unsigned_int<Width> c(bits);\n"
    "      return c;\n"
    "      \n"
    "      // unsigned_int<Width> res;\n"
    "      // unsigned char carry = 0;\n"
    "      // for (int i = 0; i < Width; i++) {\n"
    "      // 	unsigned char sum = a.get(i) + b.get(i) + carry;\n"
    "\n"
    "      // 	unsigned char z_i = sum & 0x01; //sum % 2;\n"
    "      // 	res.set(i, z_i);\n"
    "      // 	if (sum >= 2) {\n"
    "      // 	  carry = 1;\n"
    "      // 	}\n"
    "\n"
    "      // }\n"
    "\n"
    "      // return res;\n"
    "    }\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<Q >= 65, unsigned_int<Q> >::type\n"
    "    add(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "      return add_general_width(a, b);\n"
    "    }\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<(33 <= Q) && (Q <= 64), unsigned_int<Q> "
    ">::type\n"
    "    add(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "\n"
    "      //std::cout << \"a = \" << a.as_native_uint64() << std::endl;\n"
    "      //std::cout << \"b = \" << b.as_native_uint64() << std::endl;\n"
    "      bv_uint64 res = a.as_native_uint64() + b.as_native_uint64();\n"
    "\n"
    "      return unsigned_int<Width>(res);\n"
    "    }\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<(17 <= Q) && (Q <= 32), unsigned_int<Q> "
    ">::type\n"
    "    add(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "\n"
    "      //std::cout << \"a 32 bit = \" << a.as_native_uint32() << "
    "std::endl;\n"
    "      //std::cout << \"b 32 bit = \" << b.as_native_uint32() << "
    "std::endl;\n"
    "      bv_uint32 res = a.as_native_uint32() + b.as_native_uint32();\n"
    "\n"
    "      return unsigned_int<Width>(res);\n"
    "    }\n"
    "      \n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<(9 <= Q) && (Q <= 16), unsigned_int<Q> "
    ">::type\n"
    "    add(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "\n"
    "      //std::cout << \"a 16 bit = \" << a.as_native_uint16() << "
    "std::endl;\n"
    "      //std::cout << \"b 16 bit = \" << b.as_native_uint16() << "
    "std::endl;\n"
    "      bv_uint16 res = a.as_native_uint16() + b.as_native_uint16();\n"
    "\n"
    "      return unsigned_int<Width>(res);\n"
    "    }\n"
    "      \n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<(1 <= Q) && (Q <= 8), unsigned_int<Q> "
    ">::type\n"
    "    add(const unsigned_int<Width>& a,\n"
    "	const unsigned_int<Width>& b) {\n"
    "\n"
    "      bv_uint8 res = +(a.as_native_uint8()) + +(b.as_native_uint8());\n"
    "\n"
    "      return unsigned_int<Width>(res);\n"
    "    }\n"
    "      \n"
    "  };\n"
    "\n"
    "  template<int N>\n"
    "  static inline unsigned_int<N> operator+(const unsigned_int<N>& a,\n"
    "					  const unsigned_int<N>& b) {\n"
    "    return unsigned_int_operations<N>::add(a, b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline unsigned_int<N> operator-(const unsigned_int<N>& a,\n"
    "					  const unsigned_int<N>& b) {\n"
    "    return unsigned_int_operations<N>::sub(a, b);\n"
    "  }\n"
    "  \n"
    "  template<int Width>\n"
    "  class bit_vector_operations {\n"
    "  public:\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<Q >= 65, bit_vector<Q> >::type\n"
    "    land(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bit_vector<Width> a_and_b;\n"
    "      for (int i = 0; i < Width; i++) {\n"
    "	a_and_b.set(i, a.get(i) & b.get(i));\n"
    "      }\n"
    "      return a_and_b;\n"
    "\n"
    "    }\n"
    "\n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<33 <= Q && Q <= 64, bit_vector<Q> >::type\n"
    "    land(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bv_uint64 a_and_b = a.as_native_uint64() & b.as_native_uint64();\n"
    "      return bit_vector<Width>(a_and_b);\n"
    "    }\n"
    "    \n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<17 <= Q && Q <= 32, bit_vector<Q> >::type\n"
    "    land(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bv_uint32 a_and_b = a.as_native_uint32() & b.as_native_uint32();\n"
    "      return bit_vector<Width>(a_and_b);\n"
    "    }\n"
    "    \n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<9 <= Q && Q <= 16, bit_vector<Q> >::type\n"
    "    land(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bv_uint16 a_and_b = a.as_native_uint16() & b.as_native_uint16();\n"
    "      return bit_vector<Width>(a_and_b);\n"
    "    }\n"
    "    \n"
    "    template<int Q = Width>\n"
    "    static inline\n"
    "    typename std::enable_if<1 <= Q && Q <= 8, bit_vector<Q> >::type\n"
    "    land(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bv_uint8 a_and_b = a.as_native_uint8() & b.as_native_uint8();\n"
    "      return bit_vector<Width>(a_and_b);\n"
    "    }\n"
    "\n"
    "\n"
    "\n"
    "    static inline bit_vector<Width> lnot(const bit_vector<Width>& a) {\n"
    "      bit_vector<Width> not_a;\n"
    "      for (int i = 0; i < Width; i++) {\n"
    "	not_a.set(i, ~a.get(i));\n"
    "      }\n"
    "      return not_a;\n"
    "\n"
    "    }\n"
    "      \n"
    "    static inline bit_vector<Width> lor(const bit_vector<Width>& a,\n"
    "					const bit_vector<Width>& b) {\n"
    "      bit_vector<Width> a_or_b;\n"
    "      for (int i = 0; i < Width; i++) {\n"
    "	a_or_b.set(i, a.get(i) | b.get(i));\n"
    "      }\n"
    "      return a_or_b;\n"
    "\n"
    "    }\n"
    "\n"
    "    static inline\n"
    "    bit_vector<Width>\n"
    "    lxor(const bit_vector<Width>& a,\n"
    "	 const bit_vector<Width>& b) {\n"
    "      bit_vector<Width> a_or_b;\n"
    "      for (int i = 0; i < Width; i++) {\n"
    "	a_or_b.set(i, a.get(i) ^ b.get(i));\n"
    "      }\n"
    "      return a_or_b;\n"
    "\n"
    "    }\n"
    "    \n"
    "  };\n"
    "\n"
    "  template<int N>\n"
    "  static inline bit_vector<N> operator~(const bit_vector<N>& a) {\n"
    "    return bit_vector_operations<N>::lnot(a);\n"
    "  }\n"
    "  \n"
    "  template<int N>\n"
    "  static inline bit_vector<N> operator&(const bit_vector<N>& a,\n"
    "					const bit_vector<N>& b) {\n"
    "    return bit_vector_operations<N>::land(a, b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bit_vector<N> operator|(const bit_vector<N>& a,\n"
    "					const bit_vector<N>& b) {\n"
    "    return bit_vector_operations<N>::lor(a, b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bit_vector<N> operator^(const bit_vector<N>& a,\n"
    "					const bit_vector<N>& b) {\n"
    "    return bit_vector_operations<N>::lxor(a, b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator!=(const bit_vector<N>& a,\n"
    "				const bit_vector<N>& b) {\n"
    "    return !a.equals(b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator==(const unsigned_int<N>& a,\n"
    "				const unsigned_int<N>& b) {\n"
    "    return a.equals(b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator==(const signed_int<N>& a,\n"
    "				const signed_int<N>& b) {\n"
    "    return a.bits() == b.bits();\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator!=(const unsigned_int<N>& a,\n"
    "				const unsigned_int<N>& b) {\n"
    "    return !(a == b);\n"
    "  }\n"
    "  \n"
    "  template<int N>\n"
    "  static inline bool operator>(const unsigned_int<N>& a,\n"
    "			       const unsigned_int<N>& b) {\n"
    "    for (int i = N - 1; i >= 0; i--) {\n"
    "      if (a.get(i) > b.get(i)) {\n"
    "	return true;\n"
    "      }\n"
    "\n"
    "      if (a.get(i) < b.get(i)) {\n"
    "	return false;\n"
    "      }\n"
    "    }\n"
    "\n"
    "    return false;\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator<(const unsigned_int<N>& a,\n"
    "			       const unsigned_int<N>& b) {\n"
    "    if (a == b) { return false; }\n"
    "\n"
    "    return !(a > b);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator>(const signed_int<N>& a,\n"
    "			       const signed_int<N>& b) {\n"
    "    if ((a.get(N - 1) == 1) && (b.get(N - 1) == 1)) {\n"
    "      assert(false);\n"
    "    }\n"
    "\n"
    "    assert(false);\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline bool operator!=(const signed_int<N>& a,\n"
    "				const signed_int<N>& b) {\n"
    "    return !(a == b);\n"
    "  }\n"
    "  \n"
    "  template<int N>\n"
    "  static inline std::ostream&\n"
    "  operator<<(std::ostream& out, const unsigned_int<N>& a) {\n"
    "    a.print(out);\n"
    "    return out;\n"
    "  }\n"
    "\n"
    "  template<int N>\n"
    "  static inline std::ostream&\n"
    "  operator<<(std::ostream& out, const signed_int<N>& a) {\n"
    "    a.print(out);\n"
    "    return out;\n"
    "  }\n"
    "  \n"
    "  template<int LowWidth, int HighWidth>\n"
    "  signed_int<HighWidth> sign_extend(const signed_int<LowWidth>& a) {\n"
    "    signed_int<HighWidth> hw;\n"
    "\n"
    "    for (int i = 0; i < LowWidth; i++) {\n"
    "      hw.set(i, a.get(i));\n"
    "    }\n"
    "    \n"
    "    if (a.get(LowWidth - 1) == 0) {\n"
    "      \n"
    "      return hw;\n"
    "    }\n"
    "\n"
    "    for (int i = LowWidth; i < HighWidth; i++) {\n"
    "      hw.set(i, 1);\n"
    "    }\n"
    "\n"
    "    return hw;\n"
    "  }\n"
    "}\n");
}

}  // namespace CoreIR
#endif
