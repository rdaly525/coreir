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

string VWireDec(VWire w);

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

void type2VWires(Type* w, string prefix, vector<VWire>* vw);
string getPrefix(Wireable* w,string suffix);

#endif // VERILOG_HPP_
