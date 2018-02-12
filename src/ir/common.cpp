#include "coreir/ir/common.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/value.h"
#include "coreir/ir/module.h"
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
    return l.size() < r.size();
  }
  for (uint i=0; i<l.size(); ++i) {
    if (l[i] != r[i]) return l[i] < r[i];
  }
  return false;
}
bool ConnectionComp::operator() (const Connection& l, const Connection& r) const {
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

string toString(Params genparams, bool multi) {
  string ret = "(";
  vector<string> plist;
  for (auto gpair : genparams) {
    plist.push_back(gpair.first + ":" + gpair.second->toString());
  }
  string sep = multi ? ",\n  " : ", ";
  return "(" + join(plist.begin(),plist.end(),sep) + ")";
}

string toString(Values vals, bool multi) {
  string ret = "(";
  vector<string> plist;
  for (auto vpair : vals) {
    plist.push_back(vpair.first + ":" + vpair.second->toString());
  }
  string sep = multi ? ",\n  " : ", ";
  return "(" + join(plist.begin(),plist.end(),sep) + ")";
}

string toString(SelectPath path) {
  return join(path.begin(),path.end(),string("."));
}

string toString(Connection con) {
  return con.first->toString() + " <=> " + con.second->toString();
}


std::string toString(Instance* inst) {
  string ret = inst->getInstname();
  if (inst->getModuleRef()->isGenerated()) { 
    ret = ret + toString(inst->getModuleRef()->getGenArgs());
  }
  return ret + toString(inst->getModArgs()) + " : " + inst->getModuleRef()->getRefName();
}

void checkValuesAreParams(Values args, Params params) {
  bool multi = args.size() > 4 || params.size() > 4;
  ASSERT(args.size() == params.size(),"Args and params are not the same!\n Args: " + toString(args,multi) + "\nParams: " + toString(params,multi));
  for (auto const &param : params) {
    auto const &arg = args.find(param.first);
    ASSERT(arg != args.end(), "Missing Arg: " + param.first + "\nExpects Params: " + toString(params) + "\nBut only gave:" + toString(args));
    ASSERT(arg->second->getValueType() == param.second,"Param type mismatch for: " + param.first + " (" + arg->second->toString()+ " vs " + param.second->toString()+")");
  }
}

void checkValuesAreConst(Values vs) {
  for (auto v : vs) {
    ASSERT(isa<Const>(v.second),v.first + " Needs to be a const!");
  }
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
