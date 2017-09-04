#pragma once

#include "coreir.h"

namespace CoreIR {

  class WireNode {
  public:
    CoreIR::Wireable* wire;

    bool isSequential;
    bool isReceiver;

    CoreIR::Wireable* getWire() const { return wire; }

    bool operator==(const WireNode& other) const {
      return (wire == other.wire) &&
	(isSequential == other.isSequential) &&
	(isReceiver == other.isReceiver);
    }

    std::string toString() const {
      return getWire()->toString() + ", sequential ? " + std::to_string(isSequential) + ", isReceiver ? " + std::to_string(isReceiver);
    }

  };

  
}

namespace std {

  template <>
  struct hash<CoreIR::WireNode>
  {
    std::size_t operator()(const CoreIR::WireNode& k) const
    {
      using std::size_t;
      using std::hash;
      using std::string;

      return ((hash<CoreIR::Wireable*>()(k.getWire())) ^
	      hash<bool>()(k.isSequential) ^
	      hash<bool>()(k.isReceiver));
    }
  };

}  

