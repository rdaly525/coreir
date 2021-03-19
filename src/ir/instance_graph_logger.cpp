#include "coreir/ir/instance_graph_logger.hpp"
#include "coreir/ir/module.h"

namespace CoreIR {

InstanceGraphLogger::~InstanceGraphLogger() {
  return;
}

void InstanceGraphLogger::logNewInstance(std::string parent, std::string child, std::string iname) {
  assert(child != "_.passthrough");
  this->log.push_back("NI " + parent + " " + child + " " + iname);
  auto &mstorage = this->storage[parent];
  ASSERT(mstorage.count(iname)==0, "Duplicate instance " + parent + " " + child + " " + iname);
  mstorage[iname] = child;
}

void InstanceGraphLogger::logInlineInstance(std::string parent, std::string i0, std::string i1, std::string inew) {
  this->log.push_back("II " + parent + " " + i0 + " " + i1 + " " + inew);
  auto &mstorage = this->storage[parent];
  if (mstorage.count(i0) > 0) {
    //Make sure that
    try {
      std::get<InlineEntry>(mstorage[i0]);
    }
    catch (const std::bad_variant_access&) {
      ASSERT(false, "Error");
    }

  }
  else {
    mstorage[i0] = InlineEntry();
  }
  InlineEntry &ie = std::get<InlineEntry>(mstorage[i0]);
  ASSERT(ie.count(i1) ==0, "ERROR");
  ie[i1] = inew;
}

void InstanceGraphLogger::logRemoveInstance(std::string parent, std::string iname) {
  this->log.push_back("RI " + parent + " " + iname);
  ASSERT(this->storage.count(parent) > 0, "Missing Module");
  auto &mstorage = this->storage[parent];
  ASSERT(mstorage.count(iname) > 0, "Missing instance");
  mstorage.erase(iname);
}

InstancePath InstanceGraphLogger::getInstancePath(std::string mname, InstancePath ipath) {
  if (ipath.size()==0) {
    return InstancePath();
  }
  auto &mstorage = this->storage[mname];
  auto i0 = ipath.front();
  ipath.pop_front();

  InstancePath ret;
  ASSERT(mstorage.count(i0) > 0, i0 + " Does not exist in " + mname);
  try { //When the module exists
    std::string sub_mname = std::get<std::string>(mstorage[i0]);
    InstancePath sub_path = this->getInstancePath(sub_mname, ipath);
    sub_path.push_front(i0);
    return sub_path;
  }
  catch (const std::bad_variant_access&) {
    InlineEntry inlineEntry = std::get<InlineEntry>(mstorage[i0]);
    auto i1 = ipath.front();
    ipath.pop_front();
    ASSERT(inlineEntry.count(i1) > 0, i1 + " Does not exist in inline " + mname + " " + i0);
    std::string inew = inlineEntry[i1];
    ipath.push_front(inew);
    return this->getInstancePath(mname, ipath);
  }
}

void InstanceGraphLogger::print_log() {
  std::cout << "LOG" << std::endl;
  for (auto s : log) {
    std::cout << "  " << s << std::endl;
  }
  //Print Storage
  std::cout << "STORAGE" << std::endl;
  for (auto &[m, mstorage] : storage) {
    std::cout << "  " << m << std::endl;
    for (auto &[i, other] : mstorage) {
      std::cout << "    " << i << std::endl;
      try {
        auto ie = std::get<InlineEntry>(other);
        for (auto &[k, v] : ie) {
          std::cout << "      " << k << " " << v << std::endl;
        }
      }
      catch (const std::bad_variant_access&) {
        std::cout << "      "  << std::get<std::string>(other) << std::endl;
      }
    }
  }
}

}  // namespace CoreIR
