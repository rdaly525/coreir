#ifndef COREIR_DYNAMICLIBRARY_HPP_
#define COREIR_DYNAMICLIBRARY_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class DynamicLibrary {
  protected :
    std::string ext;
  private :
    std::deque<std::string> searchPaths;
    
    //Filename -> Handle
    std::map<std::string,void*> libCache;

    //Filename -> path
    std::map<std::string,std::string> pathMap;
  
  public :
    DynamicLibrary();
    ~DynamicLibrary();
    void addSearchPath(std::string path, bool front=false);
    std::string pathsToString();
    void* openLibrary(std::string fileName);
    void* getFunction(std::string fileName, std::string functionName);
};

}

#endif
