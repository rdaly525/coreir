#ifndef VERILOG_HPP_
#define VERILOG_HPP_

#include "enums.hpp"
#include <sstream>
#include <vector>
#include <cassert>
#include "coreir.hpp"

//What I need to represent
//
//Wire(string name, int bits)
//
//ModuleDec((Wire w,string dir)* puts,stmt* stmsts)
//Stmt = string
//     | WireDec(Wire w)
//     | Assigns(string left, string right)
//     | Instance(string modname,(Wire l, Wire r)*)
//
//Expr = string
//     | Wire


struct VWire {
  string name;
  unsigned dim;
  Dir dir;
  VWire(string name, unsigned dim, Dir dir);
  string dimstr();
  string dirstr();
};

// Does a Wire declaration
// wire [17:0] wname;
string VWireDec(VWire w);

//Produces an assign. 
//Can take in two VWires and correctly order them
string VAssign(string l, string r);
string VAssign(VWire a, VWire b);

struct VInstance {
  string modname;
  string instname;
  vector<std::pair<VWire,VWire>> ports;
  VInstance(string modname, string instname);
  void addport(std::pair<VWire,VWire> port);
  string toString();
};

struct VModule {
  string modname;
  vector<VWire> ports;
  vector<string> stmts;
  VModule(string modname);
  VModule(ModuleDef* m);
  void addport(VWire port);
  void addstmt(string stmt);
  string toString();
};

// Takes a type and returns an ordered list of VWires that match the type. Can pass in a prefix string "<prefix>_<VWire>"
void type2VWires(Type* w, string prefix, vector<VWire>* vw);

#endif // VERILOG_HPP_
