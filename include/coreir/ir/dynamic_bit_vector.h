#pragma once

#include <bitset>
#include <cassert>
#include <iostream>
#include <stdint.h>
#include <type_traits>

#define GEN_NUM_BYTES(N) (((N) / 8) + 1 - (((N) % 8 == 0)))
#define NUM_BYTES_GT_8(N) GEN_NUM_BYTES(N)
#define NUM_BYTES_GT_4(N) (N <= 64 ? 8 : NUM_BYTES_GT_8(N))
#define NUM_BYTES_GT_2(N) (N <= 32 ? 4 : NUM_BYTES_GT_4(N))
#define NUM_BYTES_GT_1(N) (N <= 16 ? 2 : NUM_BYTES_GT_2(N))
#define NUM_BYTES(N) (N <= 8 ? (1) : NUM_BYTES_GT_1(N))

typedef int8_t  bv_sint8;
typedef int32_t  bv_sint32;

typedef uint8_t  bv_uint8;
typedef uint16_t bv_uint16;
typedef uint32_t bv_uint32;
typedef uint64_t bv_uint64;

namespace bsim {

  static std::string hex_digit_to_binary(const char hex_digit) {
    switch (hex_digit) {
    case '0':
      return "0000";
    case '1':
      return "0001";
    case '2':
      return "0010";
    case '3':
      return "0011";
    case '4':
      return "0100";
    case '5':
      return "0101";
    case '6':
      return "0110";
    case '7':
      return "0111";
    case '8':
      return "1000";
    case '9':
      return "1001";
    case 'a':
      return "1010";
    case 'b':
      return "1011";
    case 'c':
      return "1100";
    case 'd':
      return "1101";
    case 'e':
      return "1110";
    case 'f':
      return "1111";
      
    default:
      assert(false);
    }

    assert(false);
  }

  class dynamic_bit_vector {
    std::vector<unsigned char> bits;
    int N;

  public:

    dynamic_bit_vector() : N(0) {}

    dynamic_bit_vector(const int N_) : N(N_) {
      bits.resize(NUM_BYTES(N));
      for (uint i = 0; i < bits.size(); i++) {
	bits[i] = 0;
      }
      
      for (int i = 0; i < N; i++) {
	set(i, 0);
      }
    }

    dynamic_bit_vector(const std::string& str_raw) : N(0) {
      std::string bv_size = "";
      int ind = 0;
      while (str_raw[ind] != '\'') {
        assert(isdigit(str_raw[ind]));
        bv_size += str_raw[ind];
        ind++;
      }

      assert (str_raw[ind] == '\'');

      ind++;

      char format = str_raw[ind];

      assert((format == 'b') ||
             (format == 'h') ||
             (format == 'd'));

      ind++;

      std::string digits = "";
      while (ind < ((int) str_raw.size())) {
        digits += str_raw[ind];
        ind++;
      }

      int num_bits = stoi(bv_size);
      N = num_bits;
      bits.resize(NUM_BYTES(num_bits));
      for (int i = 0; i < ((int) bits.size()); i++) {
        bits[i] = 0;
      }

      // TODO: Check that digits are not too long

      assert(format == 'h');

      int bit_ind = 0;
      for (int i = digits.size() - 1; i >= 0; i--) {
        char hex_digit = digits[i];
        std::string hex_to_binary = hex_digit_to_binary(hex_digit);

        assert(hex_to_binary.size() == 4);

        int k = 0;
        for (int j = hex_to_binary.size() - 1; j >= 0; j--) {
          // Dont add past the end
          if ((bit_ind + k) < bitLength()) {
            set(bit_ind + k, hex_to_binary[j]);
            k++;
          } else {
            assert(hex_to_binary[j] == '0');
          }
        }
        bit_ind += 4;
      }

    }

    dynamic_bit_vector(const int N_, const std::string& str_raw) : N(N_) {
      int num_digits = 0;
      std::string str;
      for (int i = 0; i < ((int) str_raw.size()); i++) {
	if (isdigit(str_raw[i])) {
	  num_digits++;
	  str += str_raw[i];
	} else {
	  assert(str_raw[i] == '_');
	}
      }
      assert(num_digits <= N);

      int len = str.size();      
      bits.resize(NUM_BYTES(N));
      for (int i = len - 1; i >= 0; i--) {
        unsigned char val = (str[i] == '0') ? 0 : 1;
        int ind = len - i - 1;
        set(ind, val);
      }
      for (int i = N-1; i>=len; i--) {
        set(i,0);
      }
    }

    dynamic_bit_vector(const int N_, const int val) : N(N_) {
      bits.resize(NUM_BYTES(N));
      *((int*) (&(bits[0]))) = val;
    }

    //dynamic_bit_vector(const int N_, const bv_uint8 val) : N(N_) {
    //  bits.resize(NUM_BYTES(N));
    //  *((bv_uint8*)(&(bits[0]))) = val;
    //}
    
    dynamic_bit_vector(const dynamic_bit_vector& other) {
      bits.resize(other.bits.size());
      N = other.bitLength();
      for (int i = 0; i < NUM_BYTES(N); i++) {
	bits[i] = other.bits[i];
      }
    }

    dynamic_bit_vector& operator=(const dynamic_bit_vector& other) {
      if (&other == this) {
    	return *this;
      }

      bits.resize(other.bits.size());

      N = other.bitLength();
      for (int i = 0; i < NUM_BYTES(N); i++) {
        bits[i] = other.bits[i];
      }


      return *this;
    }

    inline void set(const int ind, const unsigned char val) {
      int byte_num = ind / 8;
      int bit_num = ind % 8;

      unsigned char old = bits[byte_num];
      // The & 0x01 only seems to be needed for logical not
      old ^= (-(val & 0x01) ^ old) & (1 << bit_num);

      bits[byte_num] = old;
    }

    unsigned char get(const int ind) const {
      int byte_num = ind / 8;
      int bit_num = ind % 8;

      unsigned char target_byte = bits[byte_num];
      return 0x01 & (target_byte >> bit_num);
    }

    inline bool equals(const dynamic_bit_vector& other) const {

      if (other.bitLength() != this->bitLength()) {
        return false;
      }

      for (int i = 0; i < N; i++) {
	if (get(i) != other.get(i)) {
	  return false;
	}
      }

      return true;
    }

    template<typename ConvType>
    ConvType to_type() const {
      ConvType tmp = *(const_cast<ConvType*>((const ConvType*) (&(bits[0]))));
      //TODO FIXME I am a sketchy hack.
      ConvType mask = sizeof(ConvType) > bits.size() ? (1<<N)-1 : -1; 
      return tmp & mask;
    }

    inline bv_uint64 as_native_int32() const {
      return to_type<bv_sint32>();
    }
    
    inline bv_uint64 as_native_uint64() const {
      return to_type<bv_uint64>();
    }

    inline bv_uint32 as_native_uint32() const {
      return to_type<bv_uint32>();
    }

    inline bv_uint16 as_native_uint16() const {
      return to_type<bv_uint16>();
    }

    inline bv_uint8 as_native_uint8() const {
      return to_type<bv_uint8>();
    }

    inline int bitLength() const {
      return N;
    }
    
  };

  static inline std::ostream& operator<<(std::ostream& out,
					 const dynamic_bit_vector& a) {
    const int N = a.bitLength();
    for (int i = N - 1; i >= 0; i--) {
      if (a.get(i) == 0) {
	out << "0";
      } else if (a.get(i) == 1) {
	out << "1";
      } else {
	assert(false);
      }
    }

    return out;
  }

  static inline bool operator==(const dynamic_bit_vector& a,
				const dynamic_bit_vector& b) {
    return a.equals(b);
  }

  static inline unsigned char highBit(const dynamic_bit_vector& a) {
    return a.get(a.bitLength() - 1);
  }

  // template<int N>
  // class unsigned_int {
  // protected:
  //   dynamic_bit_vector<N> bits;

  // public:
  //   unsigned_int() {}

  //   unsigned_int(const std::string& bitstr) : bits(bitstr){}

  //   unsigned_int(const dynamic_bit_vector<N>& bits_) : bits(bits_) {}

  //   unsigned_int(const bv_uint8 val) : bits(val) {}
  //   unsigned_int(const bv_uint16 val) : bits(val) {}
  //   unsigned_int(const bv_uint32 val) : bits(val) {}
  //   unsigned_int(const bv_uint64 val) : bits(val) {}

  //   void set(const int ind, const unsigned char val) {
  //     bits.set(ind, val);
  //   }

  //   dynamic_bit_vector<N> get_bits() const { return bits; }    

  //   unsigned char get(const int ind) const { return bits.get(ind); }

  //   inline bool equals(const unsigned_int<N>& other) const {
  //     return (this->bits).equals((other.bits));
  //   }

  //   inline bv_uint64 as_native_uint64() const {
  //     return bits.as_native_uint64();
  //   }
    
  //   inline bv_uint32 as_native_uint32() const {
  //     return bits.as_native_uint32();
  //   }

  //   inline bv_uint16 as_native_uint16() const {
  //     return bits.as_native_uint16();
  //   }

  //   inline bv_uint8 as_native_uint8() const {
  //     return bits.as_native_uint8();
  //   }
    
  //   inline std::ostream& print(std::ostream& out) const {
  //     out << bits << "U";
  //     return out;
  //   }
    
  // };

  // template<int N>
  // class signed_int {
  // protected:
  //   dynamic_bit_vector<N> bits;

  // public:
  //   signed_int() {}


  //   signed_int(const dynamic_bit_vector<N>& bits_) : bits(bits_) {}

  //   signed_int(const int val) : bits(val) {}

  //   signed_int(const std::string& bitstr) : bits(bitstr) {}

  //   signed_int(const bv_uint8 val) : bits(val) {}
  //   signed_int(const bv_uint16 val) : bits(val) {}
  //   signed_int(const bv_uint32 val) : bits(val) {}
  //   signed_int(const bv_uint64 val) : bits(val) {}

  //   void set(const int ind, const unsigned char val) {
  //     bits.set(ind, val);
  //   }

  //   dynamic_bit_vector<N> get_bits() const { return bits; }

  //   unsigned char get(const int ind) const { return bits.get(ind); }

  //   inline bool equals(const signed_int<N>& other) const {
  //     return (this->bits).equals((other.bits));
  //   }

  //   template<int HighWidth>
  //   signed_int<HighWidth> sign_extend() const {
  //     signed_int<HighWidth> hw;

  //     for (int i = 0; i < N; i++) {
  // 	hw.set(i, get(i));
  //     }
    
  //     if (get(N - 1) == 0) {
      
  // 	return hw;
  //     }

  //     for (int i = N; i < HighWidth; i++) {
  // 	hw.set(i, 1);
  //     }

  //     return hw;
  //   }
    
  //   bv_sint32 as_native_int32() const {
  //     if (N < 32) {
  // 	signed_int<32> extended = sign_extend<32>();

  // 	dynamic_bit_vector<32> bv = extended.get_bits();

  // 	return bv.as_native_int32();
  //     }

  //     if (N == 32) {
  // 	return get_bits().as_native_int32();
  //     }

  //     assert(false);
  //   }

  //   template<typename ConvType>
  //   ConvType to_type() const {
  //     return bits.template to_type<ConvType>();
  //   }
    
  //   inline bv_uint64 as_native_uint64() const {
  //     return bits.as_native_uint64();
  //   }
    
  //   inline bv_uint32 as_native_uint32() const {
  //     return bits.as_native_uint32();
  //   }

  //   inline bv_uint16 as_native_uint16() const {
  //     return bits.as_native_uint16();
  //   }

  //   inline bv_uint8 as_native_uint8() const {
  //     return bits.as_native_uint8();
  //   }
    
  //   inline std::ostream& print(std::ostream& out) const {
  //     out << bits << "S";
  //     return out;
  //   }
    
  // };

  static inline
  dynamic_bit_vector
  add_general_width_bv(const dynamic_bit_vector& a,
  		       const dynamic_bit_vector& b) {

    dynamic_bit_vector res(a.bitLength());
    unsigned char carry = 0;
    for (int i = 0; i < ((int) a.bitLength()); i++) {
      unsigned char sum = a.get(i) + b.get(i) + carry;

      carry = 0;

      unsigned char z_i = sum & 0x01; //sum % 2;
      res.set(i, z_i);
      if (sum >= 2) {
  	carry = 1;
      }

    }

    return res;
  }

  static inline
  dynamic_bit_vector
  sub_general_width_bv(const dynamic_bit_vector& a,
  		       const dynamic_bit_vector& b) {
    int Width = a.bitLength();
    dynamic_bit_vector diff(a.bitLength());
    dynamic_bit_vector a_cpy = a;

    for (int i = 0; i < Width; i++) {

      if ((a_cpy.get(i) == 0) &&
  	  (b.get(i) == 1)) {

  	int j = i + 1;

  	diff.set(i, 1);	  

  	// Modify to carry
  	while ((j < Width) && (a_cpy.get(j) != 1)) {
  	  a_cpy.set(j, 1);
  	  j++;
  	}

  	if (j >= Width) {
  	} else {
  	  a_cpy.set(j, 0);
  	}

      } else if (a_cpy.get(i) == b.get(i)) {
  	diff.set(i, 0);
      } else if ((a_cpy.get(i) == 1) &&
  		 (b.get(i) == 0)) {
  	diff.set(i, 1);
      } else {
  	assert(false);
      }
    }

    return diff;
  }    

  static inline
  dynamic_bit_vector
  mul_general_width_bv(const dynamic_bit_vector& a,
  		       const dynamic_bit_vector& b) {
    int Width = a.bitLength();
    dynamic_bit_vector full_len(2*Width);

    for (int i = 0; i < Width; i++) {
      if (b.get(i) == 1) {

  	dynamic_bit_vector shifted_a(2*Width);

  	for (int j = 0; j < Width; j++) {
  	  shifted_a.set(j + i, a.get(j));
  	}

  	full_len =
  	  add_general_width_bv(full_len, shifted_a);
      }
    }

    dynamic_bit_vector res(Width);
    for (int i = 0; i < Width; i++) {
      res.set(i, full_len.get(i));
    }
    return res;
  }    
  
  class dynamic_bit_vector_operations {
  public:

    static inline
    dynamic_bit_vector
    land(const dynamic_bit_vector& a,
  	 const dynamic_bit_vector& b) {
      dynamic_bit_vector a_and_b(a.bitLength());
      for (int i = 0; i < a.bitLength(); i++) {
  	a_and_b.set(i, a.get(i) & b.get(i));
      }
      return a_and_b;

    }

  //   template<int Q = Width>
  //   static inline
  //   typename std::enable_if<33 <= Q && Q <= 64, dynamic_bit_vector<Q> >::type
  //   land(const dynamic_bit_vector<Width>& a,
  // 	 const dynamic_bit_vector<Width>& b) {
  //     bv_uint64 a_and_b = a.as_native_uint64() & b.as_native_uint64();
  //     return dynamic_bit_vector<Width>(a_and_b);
  //   }
    
  //   template<int Q = Width>
  //   static inline
  //   typename std::enable_if<17 <= Q && Q <= 32, dynamic_bit_vector<Q> >::type
  //   land(const dynamic_bit_vector<Width>& a,
  // 	 const dynamic_bit_vector<Width>& b) {
  //     bv_uint32 a_and_b = a.as_native_uint32() & b.as_native_uint32();
  //     return dynamic_bit_vector<Width>(a_and_b);
  //   }
    
  //   template<int Q = Width>
  //   static inline
  //   typename std::enable_if<9 <= Q && Q <= 16, dynamic_bit_vector<Q> >::type
  //   land(const dynamic_bit_vector<Width>& a,
  // 	 const dynamic_bit_vector<Width>& b) {
  //     bv_uint16 a_and_b = a.as_native_uint16() & b.as_native_uint16();
  //     return dynamic_bit_vector<Width>(a_and_b);
  //   }
    
  //   template<int Q = Width>
  //   static inline
  //   typename std::enable_if<1 <= Q && Q <= 8, dynamic_bit_vector<Q> >::type
  //   land(const dynamic_bit_vector<Width>& a,
  // 	 const dynamic_bit_vector<Width>& b) {
  //     bv_uint8 a_and_b = a.as_native_uint8() & b.as_native_uint8();
  //     return dynamic_bit_vector<Width>(a_and_b);
  //   }



    static inline dynamic_bit_vector lnot(const dynamic_bit_vector& a) {
      dynamic_bit_vector not_a(a.bitLength());
      for (int i = 0; i < a.bitLength(); i++) {
  	not_a.set(i, ~a.get(i));
      }
      return not_a;

    }
      
    static inline dynamic_bit_vector lor(const dynamic_bit_vector& a,
					 const dynamic_bit_vector& b) {
      dynamic_bit_vector a_or_b(a.bitLength());
      for (int i = 0; i < a.bitLength(); i++) {
  	a_or_b.set(i, a.get(i) | b.get(i));
      }
      return a_or_b;
    }

    static inline
    dynamic_bit_vector
    lxor(const dynamic_bit_vector& a,
  	 const dynamic_bit_vector& b) {
      dynamic_bit_vector a_or_b(a.bitLength());
      for (int i = 0; i < a.bitLength(); i++) {
  	a_or_b.set(i, a.get(i) ^ b.get(i));
      }
      return a_or_b;

    }
    
  };

  static inline dynamic_bit_vector operator~(const dynamic_bit_vector& a) {
    return dynamic_bit_vector_operations::lnot(a);
  }
  
  static inline dynamic_bit_vector operator&(const dynamic_bit_vector& a,
					     const dynamic_bit_vector& b) {
    return dynamic_bit_vector_operations::land(a, b);
  }

  static inline dynamic_bit_vector operator|(const dynamic_bit_vector& a,
					     const dynamic_bit_vector& b) {
    return dynamic_bit_vector_operations::lor(a, b);
  }

  static inline dynamic_bit_vector operator^(const dynamic_bit_vector& a,
					     const dynamic_bit_vector& b) {
    return dynamic_bit_vector_operations::lxor(a, b);
  }

  static inline bool operator!=(const dynamic_bit_vector& a,
  				const dynamic_bit_vector& b) {
    return !a.equals(b);
  }

  // template<int N>
  // static inline bool operator==(const unsigned_int<N>& a,
  // 				const unsigned_int<N>& b) {
  //   return a.equals(b);
  // }

  // template<int N>
  // static inline bool operator==(const signed_int<N>& a,
  // 				const signed_int<N>& b) {
  //   return a.get_bits() == b.get_bits();
  // }

  // template<int N>
  // static inline bool operator!=(const unsigned_int<N>& a,
  // 				const unsigned_int<N>& b) {
  //   return !(a == b);
  // }
  
  static inline bool operator>(const dynamic_bit_vector& a,
  			       const dynamic_bit_vector& b) {
    int N = a.bitLength();
    for (int i = N - 1; i >= 0; i--) {
      if (a.get(i) > b.get(i)) {
  	return true;
      }

      if (a.get(i) < b.get(i)) {
  	return false;
      }
    }

    return false;
  }

  static inline bool operator>=(const dynamic_bit_vector& a,
				const dynamic_bit_vector& b) {
    return (a > b) || (a == b);
  }
  
  static inline bool operator<(const dynamic_bit_vector& a,
  			       const dynamic_bit_vector& b) {
    if (a == b) { return false; }

    return !(a > b);
  }

  static inline dynamic_bit_vector
  andr(const dynamic_bit_vector& a) {
    for (int i = 0; i < a.bitLength(); i++) {
      if (a.get(i) != 1) {
	return dynamic_bit_vector(1, "0");
      }
    }

    return dynamic_bit_vector(1, "1");
  }

  static inline dynamic_bit_vector
  orr(const dynamic_bit_vector& a) {
    for (int i = 0; i < a.bitLength(); i++) {
      if (a.get(i) == 1) {
	return dynamic_bit_vector(1, "1");
      }
    }

    return dynamic_bit_vector(1, "0");
  }

  static inline dynamic_bit_vector
  xorr(const dynamic_bit_vector& a) {
    int numSet = 0;
    for (int i = 0; i < a.bitLength(); i++) {
      if (a.get(i) == 1) {
	numSet++;
      }
    }

    if ((numSet % 2) == 0) {
      return dynamic_bit_vector(1, "0");
    }

    return dynamic_bit_vector(1, "1");
  }
  
  // template<int N>
  // static inline bool operator<=(const unsigned_int<N>& a,
  // 				const unsigned_int<N>& b) {
  //   return !(a > b);
  // }

  // template<int N>
  // static inline bool operator>=(const unsigned_int<N>& a,
  // 				const unsigned_int<N>& b) {
  //   return (a > b) || (a == b);
  // }

  // template<int N>
  // static inline unsigned_int<N> operator/(const unsigned_int<N>& a,
  // 					  const unsigned_int<N>& b) {
  //   unsigned_int<N> quotient;
  //   unsigned_int<N> val = a;

  //   while (b <= val) {
  //     val = val - 
  //   }

  //   return quotient;
  // }

  static inline bool
  signed_gt(const dynamic_bit_vector& a,
	    const dynamic_bit_vector& b) {

    assert(a.bitLength() == b.bitLength());

    int N = a.bitLength();

    // a negative b non-negative
    if ((a.get(N - 1) == 1) && (b.get(N - 1) == 0)) {
      return false;
    }

    // b negative a non-negative
    if ((b.get(N - 1) == 1) && (a.get(N - 1) == 0)) {
      return true;
    }

    // Both negative or both non-negative
    //if ((a.get(N - 1) == 1) && (b.get(N - 1) == 1)) {

    for (int i = N - 2; i >= 0; i--) {
      if (a.get(i) > b.get(i)) {
  	return true;
      }

      if (a.get(i) < b.get(i)) {
  	return false;
      }
    }

    return false;

  }

  static inline bool signed_gte(const dynamic_bit_vector& a,
  				const dynamic_bit_vector& b) {
    return (signed_gt(a, b)) || (a == b);
  }

  static inline
  bv_uint64 get_shift_int(const dynamic_bit_vector& shift_amount) {
    bv_uint64 shift_int = 0;
    if (shift_amount.bitLength() > 64) {
      assert(false);
    }

    else if (shift_amount.bitLength() > 32) {
      shift_int = shift_amount.to_type<bv_uint64>();
    }

    else if (shift_amount.bitLength() > 16) {
      shift_int = (bv_uint64) (shift_amount.to_type<bv_uint32>());
    }

    else if (shift_amount.bitLength() > 8) {
      shift_int = (bv_uint64) (shift_amount.to_type<bv_uint16>());
    } else {
      shift_int = (bv_uint64) (shift_amount.to_type<bv_uint8>());
    }

    //std::cout << "shift_int = " << shift_int << std::endl;
    assert(shift_int < 65);

    return shift_int;
  }

  static inline dynamic_bit_vector
  lshr(const dynamic_bit_vector& a,
       const dynamic_bit_vector& shift_amount) {
    dynamic_bit_vector res(a.bitLength());

    bv_uint64 shift_int = get_shift_int(shift_amount);

    if (shift_int == 0) {
      return a;
    }

    //unsigned char sign_bit = a.get(a.bitLength() - 1);
    for (uint i = a.bitLength() - 1; i >= shift_int; i--) {
      res.set(i - shift_int, a.get(i));
    }

    for (uint i = a.bitLength() - 1; i >= (a.bitLength() - shift_int); i--) {
      res.set(i, 0);
    }

    return res;
  }

  // Arithmetic shift right
  static inline
  dynamic_bit_vector
  ashr(const dynamic_bit_vector& a,
       const dynamic_bit_vector& shift_amount) {

    if (shift_amount == dynamic_bit_vector(shift_amount.bitLength(), 0)) {
      return a;
    }

    dynamic_bit_vector res(a.bitLength());

    bv_uint64 shift_int = get_shift_int(shift_amount);

    unsigned char sign_bit = a.get(a.bitLength() - 1);
    for (uint i = a.bitLength() - 1; i >= shift_int; i--) {
      res.set(i - shift_int, a.get(i));
    }

    for (uint i = a.bitLength() - 1; i >= (a.bitLength() - shift_int); i--) {
      res.set(i, sign_bit);
    }

    return res;
  }
  
  static inline
  dynamic_bit_vector
  shl(const dynamic_bit_vector& a,
      const dynamic_bit_vector& shift_amount) {
    dynamic_bit_vector res(a.bitLength());

    bv_uint64 shift_int = get_shift_int(shift_amount);    
    for (int i = shift_int; i < a.bitLength(); i++) {
      res.set(i, a.get(i - shift_int));
    }

    return res;
  }

  static inline
  dynamic_bit_vector
  concat(const dynamic_bit_vector& a,
	 const dynamic_bit_vector& b) {
    dynamic_bit_vector res(a.bitLength() + b.bitLength());
    for (int i = 0; i < a.bitLength(); i++) {
      res.set(i, a.get(i));
    }
    for (int i = 0; i < ((int) b.bitLength()); i++) {
      res.set(i + a.bitLength(), b.get(i));
    }

    return res;
  }
  
  static inline
  dynamic_bit_vector
  slice(const dynamic_bit_vector& a,
	const int start,
	const int end) {
    dynamic_bit_vector res(end - start);

    for (int i = 0; i < res.bitLength(); i++) {
      res.set(i, a.get(i + start));
    }
    return res;
  }
  

  static inline
  dynamic_bit_vector
  extend(const dynamic_bit_vector& a, const int extra_bits) {
    dynamic_bit_vector res(a.bitLength() + extra_bits);
    for (uint i = 0; i < a.bitLength(); i++) {
      res.set(i, a.get(i));
    }

    return res;
  }

  static inline
  dynamic_bit_vector
  set_ops(const dynamic_bit_vector& a_exp,
	  const dynamic_bit_vector& b_exp,
	  const dynamic_bit_vector& a_ext,
	  const dynamic_bit_vector& b_ext,	  
	  dynamic_bit_vector& a_op,
	  dynamic_bit_vector& b_op) {

    dynamic_bit_vector tentative_exp(a_exp.bitLength());

    if (a_exp > b_exp) {
      tentative_exp = a_exp;

      auto diff = sub_general_width_bv(a_exp, b_exp);

      auto shift_b = lshr(b_ext, diff);

      a_op = a_ext;
      b_op = shift_b;

    } else {
      tentative_exp = b_exp;

      auto diff = sub_general_width_bv(b_exp, a_exp);

      auto shift_a = lshr(a_ext, diff);

      a_op = shift_a;
      b_op = b_ext;

    }

    return tentative_exp;
  }

  static inline
  dynamic_bit_vector
  renormalize_zeros(dynamic_bit_vector& sliced_sum,
		    const dynamic_bit_vector& tentative_exp,
		    const int width) {

    dynamic_bit_vector new_exp(tentative_exp.bitLength());

    int num_leading_zeros = 0;
    for (int i = sliced_sum.bitLength(); i >= 0; i--) {
      if (sliced_sum.get(i) == 1) {
	break;
      }

      num_leading_zeros++;
    }

    dynamic_bit_vector shift_w(width, num_leading_zeros);
    sliced_sum = shl(sliced_sum, shift_w);
    new_exp = sub_general_width_bv(tentative_exp, shift_w);

    std::cout << "Sum after shifting " << num_leading_zeros << " = " << sliced_sum << std::endl;

    return new_exp;
  }  

  // NOTE: This should implement "round to nearest even"
  static inline
  dynamic_bit_vector
  ieee_round(const dynamic_bit_vector& sum) {
    dynamic_bit_vector guards = slice(sum, 0, 2);
    dynamic_bit_vector last_three = slice(sum, 0, 3);

    std::cout << "to round       = " << sum << std::endl;
    std::cout << "last 3 digits  = " << last_three << std::endl;

    std::cout << "guards         =  " << guards << std::endl;

    dynamic_bit_vector upper(2, "10");

    dynamic_bit_vector res = sum;
    dynamic_bit_vector app(sum.bitLength(), "10");
    if (guards > upper) {
      res = add_general_width_bv(sum, app);
    } else if (guards == upper) {
      if (sum.get(2) == 0) {
	res = sub_general_width_bv(sum, app);
      } else {
	assert(sum.get(2) == 1);
	res = add_general_width_bv(sum, app);
      }
    }

    auto rnd_last_3 = slice(res, 0, 3);
    std::cout << "rounded last 3 = " << rnd_last_3 << std::endl;
    std::cout << "res      = " << res << std::endl;

    return res;
  }

  static inline
  dynamic_bit_vector
  floating_point_add(const dynamic_bit_vector& a,
		     const dynamic_bit_vector& b,
		     const unsigned precision_width,
		     const unsigned exp_width) {
    unsigned width = 1 + precision_width + exp_width;

    assert(a.bitLength() == width);
    assert(b.bitLength() == width);

    dynamic_bit_vector a_mant = slice(a, 0, precision_width);
    dynamic_bit_vector b_mant = slice(b, 0, precision_width);

    assert(a_mant.bitLength() == ((int) precision_width));
    assert(b_mant.bitLength() == ((int) precision_width));

    // TODO: Check normalization
    dynamic_bit_vector a_exp = slice(a,
				     precision_width,
				     precision_width + exp_width);

    dynamic_bit_vector b_exp = slice(b,
				     precision_width,
				     precision_width + exp_width);

    assert(a_exp.bitLength() == exp_width);
    assert(b_exp.bitLength() == exp_width);

    // auto a_ext = extend(a_mant, 2);
    // a_ext.set(precision_width, 1);
    // auto b_ext = extend(b_mant, 2);
    // b_ext.set(precision_width, 1);

    std::cout << "a_man      = " << a_mant << std::endl;
    std::cout << "b_man      = " << b_mant << std::endl;
    
    auto a_ext = extend(a_mant, 4);
    a_ext = shl(a_ext, dynamic_bit_vector(width, 2));
    a_ext.set(precision_width + 2, 1);

    auto b_ext = extend(b_mant, 4);
    b_ext = shl(b_ext, dynamic_bit_vector(width, 2));
    b_ext.set(precision_width + 2, 1);
    
    std::cout << "a_ext      = " << a_ext << std::endl;
    std::cout << "b_ext      = " << b_ext << std::endl;
    
    dynamic_bit_vector a_op(a_ext.bitLength());
    dynamic_bit_vector b_op(b_ext.bitLength());

    auto tentative_exp = set_ops(a_exp, b_exp,
				 a_ext, b_ext,
				 a_op, b_op);

    std::cout << "a_op       = " << a_op << std::endl;
    std::cout << "b_op       = " << b_op << std::endl;
    
    std::cout << "Operating" << std::endl;

    dynamic_bit_vector sum(a_op.bitLength());
    if ((highBit(a) == 0) && (highBit(b) == 1)) {
      sum = sub_general_width_bv(a_op , b_op);
    } else {
      sum = add_general_width_bv(a_op , b_op);
    }

    bool overflow = sum.get(sum.bitLength() - 1) == 1;

    std::cout << "sum =    " << sum << std::endl;

    dynamic_bit_vector final_sum(precision_width);

    if ((highBit(a) == 0) && (highBit(b) == 1)) {

      sum = ieee_round(sum);      

      dynamic_bit_vector sliced_sum(sum.bitLength() - 2);
      sliced_sum = slice(sum, 2, sum.bitLength() - 2);

      assert(sliced_sum.bitLength() == ((int) precision_width));

      tentative_exp = renormalize_zeros(sliced_sum, tentative_exp, width);

      final_sum = sliced_sum;

    } else {

      if (overflow) {
	//sum = ieee_round(sum);

	dynamic_bit_vector one(exp_width, 1);
	tentative_exp = add_general_width_bv(tentative_exp, one);

	auto shift_sum = ieee_round(lshr(sum, one));
	final_sum = slice(shift_sum, 2, sum.bitLength() - 2);

	std::cout << "sss =   " << final_sum << std::endl;
      } else {

	sum = ieee_round(sum);
	dynamic_bit_vector sliced_sum(sum.bitLength() - 2);
	sliced_sum = slice(sum, 2, sum.bitLength() - 2);

	assert(sliced_sum.bitLength() == ((int) precision_width));
	final_sum = sliced_sum;      
      }

    }



    dynamic_bit_vector sign_bit(1);
    sign_bit.set(0, 0);

    auto res = concat(final_sum, concat(tentative_exp, sign_bit));

    assert(res.bitLength() == width);

    return res;
  }

  
  static inline
  bool
  floating_point_gt(const dynamic_bit_vector& a,
		    const dynamic_bit_vector& b,
		    const unsigned precision_width,
		    const unsigned exp_width) {

    unsigned width = 1 + precision_width + exp_width;

    assert(a.bitLength() == width);
    assert(b.bitLength() == width);

    dynamic_bit_vector a_mant = slice(a, 0, precision_width);
    dynamic_bit_vector b_mant = slice(b, 0, precision_width);

    assert(a_mant.bitLength() == ((int) precision_width));
    assert(b_mant.bitLength() == ((int) precision_width));

    // TODO: Check normalization
    dynamic_bit_vector a_exp = slice(a,
				     precision_width,
				     precision_width + exp_width);

    dynamic_bit_vector b_exp = slice(b,
				     precision_width,
				     precision_width + exp_width);

    assert(a_exp.bitLength() == exp_width);
    assert(b_exp.bitLength() == exp_width);

    bool a_pos = highBit(a) == 0;
    bool b_pos = highBit(b) == 0;

    if (a_pos && b_pos) {

      if (a_exp > b_exp) {
	return true;
      }

      if (b_exp > a_exp) {
	return false;
      }
    

      assert(b_exp == a_exp);

      return a_mant > b_mant;
    } else if (!a_pos && !b_pos) {
      if (a_exp > b_exp) {
	return false;
      }

      if (b_exp > a_exp) {
	return true;
      }

      assert(b_exp == a_exp);

      return a_mant < b_mant;
    } else if (!a_pos && b_pos) {
      return false;
    } else if (a_pos && !b_pos) {
      return true;
    } else {
      assert(false);
    }
  }
  // template<int N>
  // static inline bool operator<=(const signed_int<N>& a,
  // 				const signed_int<N>& b) {
  //   return !(a > b);
  // }

  // template<int N>
  // static inline bool operator!=(const signed_int<N>& a,
  // 				const signed_int<N>& b) {
  //   return !(a == b);
  // }
  
  // template<int N>
  // static inline std::ostream&
  // operator<<(std::ostream& out, const unsigned_int<N>& a) {
  //   a.print(out);
  //   return out;
  // }

  // template<int N>
  // static inline std::ostream&
  // operator<<(std::ostream& out, const signed_int<N>& a) {
  //   a.print(out);
  //   return out;
  // }
  
  // template<int LowWidth, int HighWidth>
  // signed_int<HighWidth> sign_extend(const signed_int<LowWidth>& a) {
  //   signed_int<HighWidth> hw;

  //   for (int i = 0; i < LowWidth; i++) {
  //     hw.set(i, a.get(i));
  //   }
    
  //   if (a.get(LowWidth - 1) == 0) {
      
  //     return hw;
  //   }

  //   for (int i = LowWidth; i < HighWidth; i++) {
  //     hw.set(i, 1);
  //   }

  //   return hw;
  // }
}
