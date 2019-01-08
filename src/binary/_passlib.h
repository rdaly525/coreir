
#include "coreir/ir/dynamiclibrary.h"

using namespace CoreIR;
class PassLibrary : public DynamicLibrary {
  Context* c;
  //library name -> filename
  std::map<std::string,std::string> pass2file;
  public :
    PassLibrary(Context* c) : DynamicLibrary(), c(c) {
      this->addSearchPath(".");
    }
    
    //pass contains the full file
    void loadPass(std::string passFile) {
      if(pass2file.count(passFile)) {
        return;
      }
      register_pass_t registerPass = (register_pass_t) this->getFunction(passFile, "registerPass");
      Pass* p = registerPass();
      ASSERT(p,"pass is null");
      c->addPass(p);
    }
    
};
