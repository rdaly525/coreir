#ifndef IR_COMMON_HPP_
#define IR_COMMON_HPP_

namespace CoreIR {
namespace common {

template <typename T> std::size_t HashValue(const T& Hashee) {
  std::hash<T> Hasher;
  return Hasher(Hashee);
}

// Combines a hash value with a new element. See
// boost.org/doc/libs/1_55_0/doc/html/hash/reference.html#boost.hash_combine.
template <typename T> void HashCombine(const T& Combinee, std::size_t* Seed) {
  (*Seed) ^= HashValue(Combinee) + 0x9e3779b9 + (*Seed << 6) + (*Seed >> 2);
}

}  // namespace common
}  // namespace CoreIR

#endif  // IR_COMMON_HPP_
