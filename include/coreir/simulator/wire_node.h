#pragma once

#include "coreir/ir/moduledef.h"

#include "coreir/simulator/utils.h"

namespace CoreIR {

  class WireNode {
  protected:
    bool highBitsDirty;
    int threadNumber;

    CoreIR::Wireable* wire;

  public:
    bool isSequential;
    bool isReceiver;

    WireNode() :
      highBitsDirty(true), threadNumber(0), wire(nullptr), isSequential(false), isReceiver(false) {}

    WireNode(const WireNode& other) :
      highBitsDirty(other.highBitsDirty),
      threadNumber(other.threadNumber),
      wire(other.wire),
      isSequential(other.isSequential),
      isReceiver(other.isReceiver) {}
    
    WireNode(CoreIR::Wireable* wire_,
	     const bool isSequential_,
	     const bool isReceiver_) :
      highBitsDirty(true),
      threadNumber(0),
      wire(wire_),
      isSequential(isSequential_),
      isReceiver(isReceiver_) {}

    int getThreadNo() const { return threadNumber; }

    void setThreadNo(const int i) {
      threadNumber = i;
    }

    bool isOpNode() const {
      if (!isSelect(getWire())) {
	assert(isInstance(getWire()));
	return true;
      }

      assert(isSelect(getWire()));

      auto sel = toSelect(getWire());
      Wireable* p = sel->getParent();

      if (fromSelf(sel) && (!isSelect(p))) {
	return true;
      }

      return false;
    }

    WireNode& operator=(const WireNode& other) {
      if (&other == this) {
	return *this;
      }

      highBitsDirty = other.highBitsDirty;
      wire = other.wire;
      isSequential = other.isSequential;
      isReceiver = other.isReceiver;
      threadNumber = other.threadNumber;

      return *this;
    }
    
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

  bool isGraphOutput(const WireNode& w);
  bool isGraphInput(const WireNode& w);

  static inline std::string nodeString(const WireNode& w) {
    if (w.isSequential) {
      if (w.isReceiver) {
        return w.getWire()->toString() + ", receiver";
      } else {
        return w.getWire()->toString() + ", source";
      }
    }
    return w.getWire()->toString();
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
	      (hash<bool>()(k.isSequential) << 1) ^
	      (hash<bool>()(k.isReceiver) << 2) ^
	      (hash<bool>()(k.highBitsAreDirty()) << 3) ^
	      (hash<bool>()(k.getThreadNo()) << 4));

      //int threadNumber;

    }
  };

}  

