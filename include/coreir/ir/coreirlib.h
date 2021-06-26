#ifndef COREIR_COREIRLIB_HPP_
#define COREIR_COREIRLIB_HPP_

#include "coreir/ir/dynamiclibrary.h"
#include "fwd_declare.h"

namespace CoreIR {

class CoreIRLibrary : public DynamicLibrary {
  Context* c;
  // library name -> filename
  std::map<std::string, std::string> lib2file;

 public:
  CoreIRLibrary(Context* c);

  // lib contains either
  //  "<path>.ext"
  //  "libname"
  Namespace* loadLib(std::string lib);

  // Can handle loading json-only header or a dynamic library header
  void loadHeader(std::string header) {
    return;
  }
  void link(std::string header, std::string def) {
    return;
  }
};

}  // namespace CoreIR

#endif
