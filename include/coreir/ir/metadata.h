#pragma once

#include "fwd_declare.h"

using json = nlohmann::json;

namespace CoreIR {
class MetaData {
  json metadata;

 public:
  MetaData() : metadata(json::value_t::object) {}
  json& getMetaData() { return metadata; }
  bool hasMetaData() { return !metadata.empty(); }
  void setMetaData(json j) { metadata = j; }
};

}  // namespace CoreIR

