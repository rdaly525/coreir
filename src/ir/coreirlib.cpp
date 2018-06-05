
#include "coreir/ir/coreirlib.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"

using namespace std;

namespace CoreIR {

CoreIRLibrary::CoreIRLibrary(Context* c) : DynamicLibrary(), c(c) {
  this->addSearchPath(".");
  this->addSearchPath("/usr/local/lib");
  this->addSearchPath("/usr/lib");
  if (auto lpath = std::getenv("DYLD_LIBRARY_PATH")) {
    auto dyldpaths = splitString<vector<string>>(lpath,':');
    for (auto path : dyldpaths) {
      if (path !="") {
        this->addSearchPath(path);
      }
    }
  }
  if (auto lpath = std::getenv("LD_LIBRARY_PATH")) {
    auto dyldpaths = splitString<vector<string>>(lpath,':');
    for (auto path : dyldpaths) {
      if (path !="") {
        this->addSearchPath(path);
      }
    }
  }
}

Namespace* CoreIRLibrary::loadLib(string lib) {
  if (c->hasNamespace(lib)) {
    return c->getNamespace(lib);
  }
  if(lib2file.count(lib)) {
    return this->c->getNamespace(lib);
  }

  vector<string> f1parse = splitString<vector<string>>(lib,'/');
  string libfile = f1parse[f1parse.size()-1];
  vector<string> f2parse = splitString<vector<string>>(libfile,'.');

  string libname;
  string filename;
  if (f1parse.size()==1 && f2parse.size()==1) { //Just passed in the name of the library
    libname = lib;
    filename = "libcoreir-"+libname + "." + this->ext;
  }
  else if (f2parse.size()==2 && f2parse[1]==ext && libfile.substr(0,10)=="libcoreir-") { //passed in path to library
    libname = f2parse[0].substr(10,f2parse[0].length()-10);
    filename = lib;
  }
  else {
    ASSERT(0,"NYI loading lib: " + lib);
  }
  LoadLibrary_t loadLibFun = (LoadLibrary_t) this->getFunction(filename,"ExternalLoadLibrary_"+libname);
  Namespace* ns = loadLibFun(c);
  ASSERT(ns,"loading lib returned a null namespace " + lib);
  lib2file[libname] = filename;
  return ns;
}

};
