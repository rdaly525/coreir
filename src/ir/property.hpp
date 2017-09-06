#ifndef PROPERTY_HPP_
#define PROPERTY_HPP_

#include "common.hpp"
#include "json.hpp"

using json = nlohmann::json;
using namespace std;

namespace CoreIR {
class Property {
  json jprop;
  public:
  Property() = default;
    json getJson() {return jprop;}
    bool hasValue() {return !jprop.empty();}
    void setJson(json j) {jprop = j;}
};

}//CoreIR namespace

#endif // PROPERTY_HPP_
