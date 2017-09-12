#pragma once

#include "coreir.h"

namespace CoreIR {

  class WireNode {
  protected:
    bool highBitsDirty;

  public:
    CoreIR::Wireable* wire;

    bool isSequential;
    bool isReceiver;

    WireNode() :
      highBitsDirty(true), wire(nullptr), isSequential(false), isReceiver(false) {}

    WireNode(CoreIR::Wireable* wire_,
	     const bool isSequential_,
	     const bool isReceiver_) :
      // TODO: Change to true when benchmarking is done
      highBitsDirty(true),
      wire(wire_),
      isSequential(isSequential_),
      isReceiver(isReceiver_) {}
    
    CoreIR::Wireable* getWire() const { return wire; }

    bool highBitsAreDirty() const { return highBitsDirty; }

    void setHighBitsDirty(const bool val) { highBitsDirty = val; }

    bool operator==(const WireNode& other) const {
      return (wire == other.wire) &&
	(isSequential == other.isSequential) &&
	(isReceiver == other.isReceiver);
    }

    std::string toString() const {
      return getWire()->toString() + ", sequential ? " + std::to_string(isSequential) + ", isReceiver ? " + std::to_string(isReceiver);
    }

  };

  static inline WireNode combNode(CoreIR::Wireable* wire) {
    return WireNode(wire, false, false);
  }

  static inline WireNode receiverNode(CoreIR::Wireable* wire) {
    return WireNode(wire, true, true);
  }

  static inline WireNode outputNode(CoreIR::Wireable* wire) {
    return WireNode(wire, true, false);
  }
  
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

