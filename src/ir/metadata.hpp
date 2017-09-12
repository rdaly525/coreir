#ifndef METADATA_HPP_
#define METADATA_HPP_

#include "fwd_declare.hpp"
#include "json.hpp"

using json = nlohmann::json;

namespace CoreIR {
class MetaData {
  json metadata;
  public:
    MetaData() {}
    json& getMetaData() {return metadata;}
    bool hasMetaData() {return !metadata.empty();}
    void setMetaData(json j) {metadata = j;}
};

}//CoreIR namespace

#endif // METADATA_HPP_
