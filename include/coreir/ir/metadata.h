#ifndef COREIR_METADATA_HPP_
#define COREIR_METADATA_HPP_

#include "fwd_declare.h"
#include "json.h"

using json = nlohmann::json;

namespace CoreIR {
class MetaData {
  json metadata;
  public:
    MetaData() : metadata(json::value_t::object) {}
    json& getMetaData() {return metadata;}
    bool hasMetaData() {return !metadata.empty();}
    void setMetaData(json j) {metadata = j;}
};

}//CoreIR namespace

#endif // METADATA_HPP_
