#include "types.h"
#include <unordered_map>
#include <string>
//void port(string name, uint width,

//Implement or(a[8] + b[8] )
/*
int main(int argv[], int argn) {

  MAG mod = mag.new();
  PORT pa = mag.port("a",8,true);
  PORT pb = mag.port("b",8,true);
  PORT pc = mag.port("c",1,false);
  RECORD rec = mag.record([pa,pb,pc])

}
*/

int main() {
  IntType myint(7);
  myint.print();
  unordered_map<string,Type> m;
  m.emplace("a",myint);
  RecordType r(m);
  r.print();
  myint.print();

  return 0;
}

