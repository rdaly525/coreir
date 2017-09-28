#include "coreir/ir/common.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/value.h"
//#include <sstream>
//#include <iterator>

using namespace std;
namespace CoreIR {

bool isNumber(string s) {
  return s.find_first_not_of("0123456789")==string::npos;
}
bool isPower2(uint n) {
  return (n & (n-1))==0;
}

bool ConnectionComp::SPComp(const SelectPath& l, const SelectPath& r) {
  if (l.size() != r.size()) {
    return l.size() > r.size();
  }
  for (uint i=0; i<l.size(); ++i) {
    if (l[i] != r[i]) return l[i] > r[i];
  }
  return true;
}
bool ConnectionComp::operator() (const Connection& l, const Connection& r) {
  if (l.first!=r.first) return SPComp(l.first->getSelectPath(),r.first->getSelectPath());
  return SPComp(l.second->getSelectPath(),r.second->getSelectPath());
}

Connection connectionCtor(Wireable* a, Wireable* b) {
  if (ConnectionComp::SPComp(a->getSelectPath(),b->getSelectPath())) {
    return Connection(a,b);
  }
  else {
    return Connection(b,a);
  }
}

string Params2Str(Params genparams) {
  string ret = "(";
  for (auto it=genparams.begin(); it!=genparams.end(); ++it) {
    ret = ret + (it==genparams.begin() ? "" : ",") + it->first + ":"+it->second->toString();
  }
  return ret + ")";
}

string Values2Str(Values args) {
  string s = "(";
  for (auto it=args.begin(); it!=args.end(); ++it) {
    s = s + (it==args.begin() ? "" : ",") + it->first + ":"+it->second->toString();
  }
  return s + ")";
}
string SelectPath2Str(SelectPath path) {
  return join(path.begin(),path.end(),string("."));
}

string Connection2Str(Connection con) {
  return con.first->toString() + " <=> " + con.second->toString();
}

void checkValuesAreParams(Values args, Params params) {
  ASSERT(args.size() == params.size(),"Args and params are not the same!\n Args: " + Values2Str(args) + "\nParams: " + Params2Str(params));
  for (auto const &param : params) {
    auto const &arg = args.find(param.first);
    ASSERT(arg != args.end(), "Arg Not found: " + param.first );
    ASSERT(arg->second->getValueType() == param.second,"Param type mismatch for: " + param.first + " (" + arg->second->toString()+ " vs " + param.second->toString()+")");
  }
}

void checkValuesAreParams(Consts args, Params params) {
  checkValuesAreParams(castMap<Value>(args),params);
}

vector<string> splitRef(string s) {
  auto p = splitString<vector<string>>(s,'.');
  ASSERT(p.size()==2,s + " is not a valid Ref");
  return p;
}

bool hasChar(const std::string s, char c) {
  return s.find_first_of(c) !=string::npos;
}

//merge a1 into a0
void mergeValues(Values& a0, Values a1) {
  for (auto arg : a1) {
    if (a0.count(arg.first)==0) {
      a0.insert(arg);
    }
  }
}

} //CoreIR namespace
