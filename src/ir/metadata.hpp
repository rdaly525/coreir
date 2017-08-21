#ifndef METADATA_HPP_
#define METADATA_HPP_

#include <unordered_map>
#include "common.hpp"
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {
class MetaData {
  json metadata;
  public:
    MetaData() {}
    //Metadata(string file,uint line) {
    //  metadata["file"] = file;
    //  metadata["line"] = to_string(line);
    //}
    json& getMetaData() {return metadata;}
    bool hasMetaData() {return !metadata.empty();}
    void setMetaData(json j) {metadata = j;}
};

}//CoreIR namespace

#endif // METADATA_HPP_
