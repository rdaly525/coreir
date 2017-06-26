#include "coreir-pass/passes.h"

using namespace CoreIR;

bool PassManager::run() {
  //For now I have to do only the modules.
  bool modified = false;
  for (auto modmap : ns->getModules()) {
    string s = modmap.first;
    Module* m = modmap.second;
    for (auto mPasses : modulePassMap) {
      cout << mPasses.first << endl;
      for (auto mp : mPasses.second) {
        modified |= mp->runOnModule(m);
      }
    }
  }
  return modified;
}


PassManager::~PassManager() {
  for (auto mPasses : modulePassMap) {
    for (auto mp : mPasses.second) {
      if (mp) delete mp;
    }
  }
}

Pass::~Pass() {}
