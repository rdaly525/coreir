#ifndef VERILOG_CPP_
#define VERILOG_CPP_

#include "enums.hpp"
#include <sstream>
#include "verilog.hpp"
#include <vector>
#include "typedcoreir.hpp"
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


VWire::VWire(string name, unsigned dim, Dir dir) : name(name), dim(dim), dir(dir) {}
string VWire::dimstr() { return "["+to_string(dim-1)+":0]";}
string VWire::dirstr() { return (dir==IN) ? "input" : "output"; }

string VWireDec(VWire w) { return "  wire " + w.dimstr() + " " + w.name + ";"; }

string VAssign(string l, string r) { return "  assign " + l + " = " + r+";";}
string VAssign(VWire a, VWire b) {
  VWire left = a.dir==IN ? a : b;
  VWire right = a.dir==IN ? b : a;
  assert(right.dir==OUT);
  assert(left.dir==IN);
  return VAssign(left.name,right.name);
}


VInstance::VInstance(string modname, string instname) : modname(modname), instname(instname) {}
void VInstance::addport(std::pair<VWire,VWire> port) { ports.push_back(port);}
string VInstance::toString() {
    ostringstream o;
    string tab = "  ";
    o << tab << modname << " " << instname << "(" << endl;
    for (auto& p : ports) {
      o << tab << tab << "." << p.first.name << "(" << p.second.name << p.second.dimstr() << ")";
      if (&p != &ports.back() ) o << ",";
      o << endl;
    }
    o << tab << ");" << endl;
    return o.str();
}

VModule::VModule(ModuleDef* m) {
  modname = m->getName();
  type2VWires(m->getType(),"",&ports);
}
VModule::VModule(string modname) : modname(modname) {}
void VModule::addport(VWire port) { ports.push_back(port); }
void VModule::addstmt(string stmt) { stmts.push_back(stmt); }
string VModule::toString() {
    ostringstream o;
    string tab = "  ";
    o << "module " << modname << "(" << endl;
    for (auto& s : ports) {
      o << tab << tab << s.dirstr() << " " << s.dimstr() << " " << s.name;
      if (&s != &ports.back() ) o << ",";
      o << endl;
    }
    o << ");" << endl << endl;
    for (auto s : stmts) o << s << endl;
    o << endl << "endmodule" << endl;
    return o.str();
}

void type2VWires(Type* t, string prefix, vector<VWire>* vw) {
  if (t->isBase()) {
    BaseType* bt = (BaseType*) t;
    VWire vwire = VWire(prefix,bt->numBits(),bt->getDir());
    vw->push_back(vwire);
    return;
  }
  if (prefix != "") prefix = prefix+"_";
  if(t->isKind(ARRAY)) {
    ArrayType* ta = (ArrayType*)t;
    for (uint i=0; i<ta->getLen(); i++) {
      string is = to_string(i);
      type2VWires(ta->sel(i),prefix+is,vw);
    }
  }
  else if(t->isKind(RECORD)) {
    RecordType* tr = (RecordType*)t;
    for (auto selstr : tr->getOrder() ) {
      type2VWires(tr->sel(selstr),prefix+selstr,vw);
    }
  }
}




#endif // VERILOG_CPP_
