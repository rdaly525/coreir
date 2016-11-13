#include "types.h"
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
  IntType myint(7,true);
  ArrayType myArray(&myint,5);
  myint.print();
  myArray.print();
  map<string,Type*> m;
  m.emplace("a",&myint);
  m.emplace("b",&myArray);
  RecordType r(m);
  r.print();

  return 0;
}

