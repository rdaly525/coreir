#ifndef METADATA_HPP_
#define METADATA_HPP_

#include <unordered_map>
#include "common.hpp"
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {
struct Metadata {
  unordered_map<string,string> metadata;
  Metadata() { metadata["_testing"] = "metadata";}
  Metadata(string file,uint line) {
    metadata["file"] = file;
    metadata["line"] = to_string(line); // TODO
  }
  json toJson();
};

}//CoreIR namespace

#endif // METADATA_HPP_
