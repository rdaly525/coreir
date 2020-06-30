
#include "coreir/ir/dynamiclibrary.h"
#include "coreir/ir/common.h"

#include <dlfcn.h>
#include <fstream>
#include <sys/utsname.h>

#if defined(__linux__)
#include <dlfcn.h>
#include <link.h>
#endif  // __linux__

using namespace std;

#if !defined(__linux__)
namespace {
bool fileExists(string name) {
  // return true;
  std::ifstream infile(name);
  return infile.good();
}
}  // namespace
#endif  // !__linux__

namespace CoreIR {

DynamicLibrary::DynamicLibrary() {
  struct utsname unameData;
  assert(!uname(&unameData));
  string osname = unameData.sysname;
  if (osname == "Darwin") { this->ext = "dylib"; }
  else if (osname == "Linux") {
    this->ext = "so";
  }
  else {
    ASSERT(0, "Cannot support OS " + osname);
  }
}
DynamicLibrary::~DynamicLibrary() {
  for (auto lcpair : libCache) { dlclose(lcpair.second); }
}
void DynamicLibrary::addSearchPath(string path, bool front) {
  if (front) { searchPaths.push_front(path); }
  else {
    searchPaths.push_back(path);
  }
}
string DynamicLibrary::pathsToString() {
  return join(searchPaths.begin(), searchPaths.end(), string("\n  "));
}
void* DynamicLibrary::openLibrary(string fileName) {
  if (libCache.count(fileName)) { return libCache[fileName]; }

#if !defined(__linux__)
  string file;
  string foundPath;
  bool found = false;
  for (auto path : searchPaths) {
    file = path + "/" + fileName;
    if (fileExists(file)) {
      found = true;
      foundPath = path;
      break;
    }
  }
  ASSERT(
    found,
    "Cannot find library " + fileName + " in paths:\n  " + pathsToString());
#endif  // !__linux__

  void* handle = dlopen(fileName.c_str(), RTLD_LAZY);
  ASSERT(handle, "dlopen error " + fileName + " " + string(dlerror()));

#if defined(__linux__)
  struct link_map* linkMap;
  int ret = dlinfo(handle, RTLD_DI_LINKMAP, &linkMap);
  ASSERT(ret == 0, "dlinfo error " + fileName + " " + string(dlerror()));
  string foundPath = linkMap->l_name;
#endif

  pathMap[fileName] = foundPath;
  libCache[fileName] = handle;
  return handle;
}
void* DynamicLibrary::getFunction(string fileName, string functionName) {
  void* handle = this->openLibrary(fileName.c_str());
  void* function = dlsym(handle, functionName.c_str());
  const char* dlsym_error = dlerror();
  ASSERT(
    !dlsym_error,
    "Cannot load function " + functionName + " from " + pathMap[fileName] +
      "\n" + string(dlsym_error));
  ASSERT(function, "function is null");
  return function;
}

};  // namespace CoreIR
