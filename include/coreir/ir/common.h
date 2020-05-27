#ifndef COREIR_COMMON_HPP_
#define COREIR_COMMON_HPP_

#include "fwd_declare.h"

// TODO stupid hack
#include "casting/casting.h"

namespace CoreIR {

// TODO Ugly hack to create a sorted connection. Should make my own connection
// class
Connection connectionCtor(Wireable* a, Wireable* b);

typedef std::set<Connection, ConnectionCompFast> ConnectionsFast;

// These are defined in helpers
bool isNumber(std::string s);
bool isPower2(uint n);

bool isSlice(std::string selstr);
std::pair<int, int> parseSlice(const std::string& selstr);

// Used to make sure string formats are valid for inst names, module names, etc
void checkStringSyntax(std::string& str);

// Checks that the values are of the correct names and types
void checkValuesAreParams(
  Values args,
  Params params,
  std::string errstring = "");

bool doValuesMatchParams(Values args, Params params);

BitVector hexStringToBitVector(const std::string& str);
// Checks that all the values are actually constants
void checkValuesAreConst(Values vs);

bool hasChar(const std::string s, char c);

std::string toString(Params, bool multi = false);
std::string toString(Values, bool multi = false);
std::string toString(SelectPath path);
std::string toString(Connection con);
std::string toString(Instance* inst);
std::string toString(RecordParams rp);

template <class T> std::string toString(const T& t) {
  std::ostringstream stream;
  stream << t;
  return stream.str();
}

template <typename BackInserter>
BackInserter splitString(const std::string& s, char delim) {
  BackInserter elems;
  std::stringstream ss;
  ss.str(s);
  std::string item;
  while (std::getline(ss, item, delim)) { elems.push_back(item); }
  return elems;
}

std::vector<std::string> splitStringByWhitespace(std::string const& input);

template <class T, class A> T join(const A& begin, const A& end, const T& t) {
  T result;
  for (A it = begin; it != end; it++) {
    if (!result.empty()) result.append(t);
    result.append(*it);
  }
  return result;
}

std::vector<std::string> splitRef(std::string s);

// Does not include
static std::map<std::string, std::set<std::string>> coreMap({
  {"unary", {"wire", "not", "neg"}},
  {"unaryReduce", {"andr", "orr", "xorr"}},
  {"binary",
   {"add",
    "sub",
    "and",
    "or",
    "xor",
    "shl",
    "lshr",
    "ashr",
    "mul",
    "udiv",
    "urem",
    "sdiv",
    "srem",
    "smod"}},
  {"binaryReduce",
   {"eq", "neq", "slt", "sgt", "sle", "sge", "ult", "ugt", "ule", "uge"}},
  {"muxType", {"mux"}},
});

void mergeValues(Values& v0, Values v1);

template <typename ContainerT, typename PredicateT>
ContainerT filterOver(const ContainerT& container, PredicateT predicate) {
  ContainerT result;
  std::copy_if(
    container.begin(),
    container.end(),
    std::inserter(result, result.end()),
    predicate);
  return result;
}

template <typename ContainerT, typename PredicateT>
bool anyOf(const ContainerT& container, PredicateT predicate) {
  return std::any_of(container.begin(), container.end(), predicate);
}

template <typename ContainerT, typename PredicateT>
bool allOf(const ContainerT& container, PredicateT predicate) {
  return std::all_of(container.begin(), container.end(), predicate);
}

// Compare select paths
bool SPComp(const SelectPath& l, const SelectPath& r);

}  // namespace CoreIR

#endif
