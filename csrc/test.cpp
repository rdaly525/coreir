#include "types.h"
#include <unordered_map>
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
  Type *type = new Type("base");
  IntType *myint = new IntType(7);
  cout << type->getType() << "\n";
  cout << myint->getType() << myint->numBits() << "\n";
  cout << __cplusplus << std::endl;

  //unordered_map<string,int> m;
  ////m.emplace("a",myint);
  //m.emplace("a",5);
  //RecordType *r = new RecordType(m);
  
  return 0;
}

