#include "coreir.h"
#include <cassert>
#include "coreir/ir/json.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  // TODO should test a bunch of other permutations
  Values g1 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g2 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g3 = {{"c",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g4 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")},{"c",Const::make(c,c->BitIn())}};
  assert(g1 == g2);
  checkValuesAreParams(g1,{{"a",c->Int()},{"b",c->String()}});
  assert(g1 != g3);
  assert(g1 != g4);
  checkValuesAreParams(g4,{{"a",c->Int()},{"b",c->String()},{"c",CoreIRType::make(c)}});
  
  Json jdata;
  jdata["mylist"][0] = 5;
  jdata["mylist"][1] = "string";
  jdata["mylist"][2] = {{"a",13},{"b",2}};
  Values g5 = {{"a",Const::make(c,jdata)}};
  checkValuesAreParams(g5,{{"a",JsonType::make(c)}});
  cout << "jsonval: " << jdata << endl;
  cout << "jsonval2: " << g5.at("a")->get<Json>() << endl;
  assert(Const::make(c,jdata) == Const::make(c,jdata));
  deleteContext(c);
  return 0;
}
