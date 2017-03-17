#include "context.hpp"
#include "passes.hpp"

using namespace CoreIR;

int main(int argc, char *argv[]){
  Context* c = newContext();

  if(argc<=1){
    cout << "usage: typecheck file1.json file2.json ..." << endl;
    return 1;
  }

  bool err = false;

  Module* m = loadModule(c,argv[1],&err);
  if(err){c->die();}

  typecheck(c,m,&err);

  if(err){
    cout << "failed typechecking!" << endl;
    return 1;
  }

  cout << "typecheck OK!" << endl;
  return 0;
}
