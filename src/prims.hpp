#ifndef PRIMS_HPP_
#define PRIMS_HPP_

makeUintBinop(uint n,string op, string symbol) {
  vstring = createVerilogBinop(n,op,symbol,"inA","inB","out");
  return new Primitive(op+to_string(n))
}

template<typename T>
void f(T


string createVerilogBinop(uint n, string op, string symbol, string a, string b, string out) {
  cassert(n>0);
  string range = "[" + to_string(n-1) + ":0]";
  string inA = "input " + range + a;
  string inB = "input " + range + b;
  string mod = "module " + op + "(" + inA + "," + inA + "," + out ")";
  string assign = "assign " + out + "= " + a + symbol + b;
  return  mod + "\n" + assign + "\n" + "endmodule";
}


//module add(input [5:0] inA, input [5:0] inB, output [5:0] out);
//  assign out = inA + inB;
//endmodule

castUp :: uint(N) -> uint(N+K);
castDown :: uint(N+K) -> uint(N);

UAdd :: uint(N) -> uint(N) -> uint(N+1);
Add :: int(N) -> int(N) -> int(N+1);
*USub
*Sub
UMult :: uint(N) ->



































