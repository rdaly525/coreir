#include "coreir/ir/common.h"
#include "coreir/ir/module.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"
#include "coreir/ir/valuetype.h"
#include "coreir/ir/wireable.h"

#include <cxxabi.h>
#include <dlfcn.h>
#include <execinfo.h>
#include <regex>

// (with modifications) taken from
// https://gist.github.com/fmela/591333/c64f4eb86037bb237862a8283df70cdfc25f01d3
void print_stack_trace(int skip) {
  void* callstack[128];
  const int nMaxFrames = sizeof(callstack) / sizeof(callstack[0]);
  char buf[1024];
  int nFrames = backtrace(callstack, nMaxFrames);
  char** symbols = backtrace_symbols(callstack, nFrames);

  std::ostringstream trace_buf;
  for (int i = skip; i < nFrames; i++) {
    Dl_info info;
    if (dladdr(callstack[i], &info)) {
      char* demangled = NULL;
      int status;
      demangled = abi::__cxa_demangle(info.dli_sname, NULL, 0, &status);
      snprintf(
        buf,
        sizeof(buf),
        "%-3d %*p %s + %zd\n",
        i,
        (int)(2 + sizeof(void*) * 2),
        callstack[i],
        status == 0 ? demangled : info.dli_sname,
        (char*)callstack[i] - (char*)info.dli_saddr);
      free(demangled);
    }
    else {
      snprintf(
        buf,
        sizeof(buf),
        "%-3d %*p\n",
        i,
        (int)(2 + sizeof(void*) * 2),
        callstack[i]);
    }
    trace_buf << buf;
  }
  free(symbols);
  if (nFrames == nMaxFrames) trace_buf << "[truncated]\n";
  std::cerr << trace_buf.str() << std::endl;
}

using namespace std;
namespace CoreIR {

// TODO get this to work with coreir_unreachable()
// void coreir_unreachable_internal(const char* file=nullptr, unsigned line=0)
//{
//  std::cerr << "Reached the Unreachable!\n";
//  if (file) {
//    std::cerr << " at "  << file << ":" << line;
//  }
//  abort();
//#ifdef LLVM_BUILTIN_UNREACHABLE
//  LLVM_BUILTIN_UNREACHABLE;
//#endif
//}

bool isNumber(string s) {
  return !s.empty() && s.find_first_not_of("0123456789") == string::npos;
}
bool isPower2(uint n) { return (n & (n - 1)) == 0; }

bool SPComp(const SelectPath& l, const SelectPath& r) {
  string ls = toString(l);
  string lr = toString(r);
  return ls < lr;
}

bool ConnectionCompFast::operator()(const Connection& l, const Connection& r)
  const {
  if (l.first != r.first) { return l.first < r.first; }
  return l.second < r.second;
}

bool ConnectionCompConsistent::operator()(
  const Connection& l,
  const Connection& r) const {
  string ls = toString(l);
  string rs = toString(r);
  return ls < rs;
}

// Creates a connection with no consistency guarentee
Connection connectionCtor(Wireable* a, Wireable* b) {
  if (a < b) { return {a, b}; }
  else {
    return {b, a};
  }
}

string toString(Params genparams, bool multi) {
  string ret = "(";
  vector<string> plist;
  for (auto gpair : genparams) {
    plist.push_back(gpair.first + ":" + gpair.second->toString());
  }
  string sep = multi ? ",\n  " : ", ";
  return "(" + join(plist.begin(), plist.end(), sep) + ")";
}

string toString(Values vals, bool multi) {
  string ret = "(";
  vector<string> plist;
  for (auto vpair : vals) {
    plist.push_back(vpair.first + ":" + vpair.second->toString());
  }
  string sep = multi ? ",\n  " : ", ";
  return "(" + join(plist.begin(), plist.end(), sep) + ")";
}

string toString(SelectPath path) {
  return join(path.begin(), path.end(), string("."));
}

// This will always be consistent
string toString(Connection con) {
  bool order = SPComp(con.first->getSelectPath(), con.second->getSelectPath());
  Wireable* fstCon = order ? con.first : con.second;
  Wireable* sndCon = order ? con.second : con.first;
  return fstCon->toString() + " <=> " + sndCon->toString();
}

string toString(RecordParams rp) {
  vector<string> ss;
  for (auto r : rp) { ss.push_back(r.first + ": " + r.second->toString()); }
  return "(" + join(ss.begin(), ss.end(), string(",")) + ")";
}

std::string toString(Instance* inst) {
  string ret = inst->getInstname();
  if (inst->getModuleRef()->isGenerated()) {
    ret = ret + toString(inst->getModuleRef()->getGenArgs());
  }
  return ret + toString(inst->getModArgs()) + " : " +
    inst->getModuleRef()->getRefName();
}

namespace {
inline bool syntaxW(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c == '_') ||
    (c == '-') || (c == '$');
}
inline bool syntaxWN(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || (c == '_') || (c == '-') || (c == '$');
}
}  // namespace

static std::string regex_str("^[a-zA-Z_\\-\\$][a-zA-Z0-9_\\-\\$]*");
void checkStringSyntax(std::string& str) {
  // static regex reg(regex_str, std::regex_constants::basic);
  ASSERT(
    syntaxW(str[0]),
    str +
      " 0: is not a valid coreIR name!. Needs to be = " + string(regex_str));
  for (uint i = 1; i < str.length(); ++i) {
    ASSERT(
      syntaxWN(str[i]),
      str + " " + to_string(i) +
        " is not a valid coreIR name!. Needs to be = " + string(regex_str));
  }
  // ASSERT(regex_search(str,syntaxreg),str+" is not a valid coreIR name!. Needs
  // to be = " + string(regex_str));
}

void checkValuesAreParams(Values args, Params params, string errstring) {
  bool multi = args.size() > 4 || params.size() > 4;
  ASSERT(
    args.size() == params.size(),
    "Args and params are not the same!\n Args: " + toString(args, multi) +
      "\nParams: " + toString(params, multi) + "\n" + errstring);
  for (auto const& param : params) {
    Context* c = param.second->getContext();
    auto const& arg = args.find(param.first);
    ASSERT(
      arg != args.end(),
      "Missing Arg: " + param.first + "\nExpects Params: " + toString(params) +
        "\nBut only gave:" + toString(args) + "\n" + errstring);
    if (param.second == AnyType::make(c)) { continue; }
    ValueType* vt = arg->second->getValueType();
    ASSERT(
      vt == param.second,
      "Param type mismatch for: " + param.first + " (" +
        arg->second->toString() + " vs " + param.second->toString() + ")" +
        "\n" + errstring);
  }
}

bool doValuesMatchParams(Values args, Params params) {
  if (args.size() != params.size()) { return false; }
  for (auto ppair : params) {
    Context* c = ppair.second->getContext();
    string pname = ppair.first;
    ValueType* param = ppair.second;
    if (args.count(pname) == 0) return false;
    if (param == AnyType::make(c)) continue;
    ValueType* vt = args[pname]->getValueType();
    if (vt != param) return false;
  }
  return true;
}

void checkValuesAreConst(Values vs) {
  for (auto v : vs) {
    ASSERT(isa<Const>(v.second), v.first + " Needs to be a const!");
  }
}

std::vector<std::string> splitStringByWhitespace(std::string const& input) {
  std::istringstream buffer(input);
  std::vector<std::string> ret(
    (std::istream_iterator<std::string>(buffer)),
    std::istream_iterator<std::string>());
  return ret;
}

vector<string> splitRef(string s) {
  auto p = splitString<vector<string>>(s, '.');
  ASSERT(p.size() == 2, s + " is not a valid Ref");
  return p;
}

bool hasChar(const std::string s, char c) {
  return s.find_first_of(c) != string::npos;
}

// merge a1 into a0
void mergeValues(Values& a0, Values a1) {
  for (auto arg : a1) {
    if (a0.count(arg.first) == 0) { a0.insert(arg); }
  }
}

}  // namespace CoreIR
