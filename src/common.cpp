#include "common.hpp"
#include <string>
#include <sstream>
#include <vector>
#include <iterator>

//#include "coreir.hpp"
//#include "typedcoreir.hpp"
#include "args.hpp"

using namespace std;
namespace CoreIR {

bool isNumber(string s) {
  return s.find_first_not_of("0123456789")==string::npos;
}


string Param2Str(Param genparam) {
  switch(genparam) {
    case AINT : return "int";
    case ASTRING : return "string";
    case ATYPE : return "type";
    default : return "NYI";
  }
}
Param Str2Param(string s) {
  if (s=="int") return AINT;
  if (s=="string") return ASTRING;
  if (s=="type") return ATYPE;
  throw std::runtime_error("Cannot convert " + s + " to Param"); 
}

string Params2Str(Params genparams) {
  string ret = "(";
  for (auto it=genparams.begin(); it!=genparams.end(); ++it) {
    
    ret = ret + it->first + ": " + Param2Str(it->second) + ((it==genparams.begin()) ? "" : ",");
  }
  return ret + ")";
}

string Args2Str(Args args) {
  string s = "(";
  for (auto it=args.begin(); it!=args.end(); ++it) {
    s = s + (it==args.begin() ? "" : ",") + it->first + ":"+it->second->toString();
  }
  return s + ")";
}
string SelectPath2Str(SelectPath s) {
  string ret = "";
  for (auto it=s.begin(); it!=s.end(); ++it) {
    ret = ret + (it==s.begin() ? "" : ".") + *it;
  }
  return ret;
}

void checkArgsAreParams(Args args, Params params) {
  ASSERT(args.size() == params.size(),"Args and params are not the same!\n Args: " + Args2Str(args) + "\nParams: " + Params2Str(params));
  for (auto const &param : params) {
    auto const &arg = args.find(param.first);
    ASSERT(arg != args.end(), "Arg Not found: " + param.first );
    ASSERT(arg->second->getKind() == param.second,"Param type mismatch for: " + param.first);
  }
}



std::vector<std::string> splitString(const std::string &s, char delim) {
    std::vector<std::string> elems;
    std::stringstream ss;
    ss.str(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
      elems.push_back(item);
    }
    return elems;
}

bool hasChar(const std::string s, char c) {
  return s.find_first_of(c) !=string::npos;
}


} //CoreIR namespace
