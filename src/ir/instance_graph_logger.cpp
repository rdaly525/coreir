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
  mstorage.emplace(iname, InstInfo(child));
}

void InstanceGraphLogger::logInlineInstance(std::string parent, std::string i0, std::string i1, std::string inew) {
  this->log.push_back("II " + parent + " " + i0 + " " + i1 + " " + inew);
  auto &mstorage = this->storage[parent];
  ASSERT(mstorage.count(i0) > 0, "Missing instance " + parent + " " + i0);
  auto &iinfo = mstorage.at(i0);
  iinfo.is_inlined = true;
  iinfo.inline_info.emplace(i1, inew);
}

void InstanceGraphLogger::logRemoveInstance(std::string parent, std::string iname) {
  this->log.push_back("RI " + parent + " " + iname);
}

InstancePath InstanceGraphLogger::getInstancePath(std::string mname, InstancePath ipath) {
  if (ipath.size()==0) {
    return InstancePath();
  }
  auto &mstorage = this->storage[mname];
  auto i0 = ipath.front();
  ipath.pop_front();

  ASSERT(mstorage.count(i0) > 0, i0 + " Does not exist in " + mname);

  auto &iinfo = mstorage.at(i0);
  //not inlined
  if (!iinfo.is_inlined) {
    std::string sub_mname = iinfo.module;
    InstancePath sub_path = this->getInstancePath(sub_mname, ipath);
    sub_path.push_front(i0);
    return sub_path;
  }
  else { //Inlined
    auto i1 = ipath.front();
    if (iinfo.inline_info.count(i1) > 0) { //Inline info exists (Top Down)
      std::string inew = iinfo.inline_info[i1];
      ipath.pop_front();
      ipath.push_front(inew);
      return this->getInstancePath(mname, ipath);
    }
    else { //Info does not exist (Bottom Up)
      //Recursively get the translation from the instance's original module
      auto sub_path = this->getInstancePath(iinfo.module, ipath);

      //Now, try the translation again within this curent module
      sub_path.push_front(i0);
      return this->getInstancePath(mname, sub_path);
    }
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
    for (auto &[i, iinfo] : mstorage) {
      std::cout << "    " << i << " " << iinfo.module << " Inlined?" << iinfo.is_inlined << std::endl;
      for (auto &[k, v] : iinfo.inline_info) {
        std::cout << "      " << k << " " << v << std::endl;
      }
    }
  }
}

}  // namespace CoreIR
