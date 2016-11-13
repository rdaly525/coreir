#include "types.hpp"
#include <map>
#include <string>
//void port(string name, uint width,

//Implement or(a[8] + b[8] )
/*
int main(int argv[], int argn) {
  
  MAG mod = mag.new();
  IFACE pa = mag.port("a",8,true);
  PORT pb = mag.port("b",8,true);
  PORT pc = mag.port("c",1,false);
  RECORD rec = mag.record([pa,pb,pc])

}
*/

int main() {
  IntType* int7 = Int(7,IN);
  ArrayType* ar5 = Array(int7,5);
  int7->print();
  ar5->print();
  //map<string,Type*> m;
  //m.emplace("a",&myint);
  //m.emplace("b",&myArray);
  //RecordType r(m);
  //r.print();

  return 0;
}

