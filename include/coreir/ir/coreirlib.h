#ifndef COREIR_COREIRLIB_HPP_
#define COREIR_COREIRLIB_HPP_

#include "fwd_declare.h"
#include "coreir/ir/dynamiclibrary.h"

namespace CoreIR {

class CoreIRLibrary : public DynamicLibrary {
  Context* c;
  //library name -> filename
  std::map<std::string,std::string> lib2file;
  public :
    CoreIRLibrary(Context* c);
   
    //lib contains either 
    //  "<path>.ext" 
    //  "libname" 
    Namespace* loadLib(std::string lib);   
};

}

#endif
