#pragma once

#include "coreir/simulator/wire_node.h"

namespace CoreIR {

  class InstanceValue {
  protected:
    // Allow an array of wires for SIMD experiments?
    CoreIR::Select* wire;

    bool mustMask;

  public:

    InstanceValue() : wire(nullptr), mustMask(true) {}

    InstanceValue(Select* wire_) : wire(wire_), mustMask(true) {}

    CoreIR::Select* getWire() const { return wire; }

    bool needsMask() const { return mustMask; }

    void setNeedsMask(const bool val) {
      mustMask = val;
    }
  };

  typedef InstanceValue WireableNode;

  typedef std::pair<WireableNode, WireableNode> Conn;

  typedef int vdisc;
  typedef int edisc;

  template<typename Node, typename Edge>
  class DirectedGraph {

    std::vector<edisc> edges;
    std::vector<vdisc> verts;

    std::map<vdisc, std::vector<edisc> > adjacent_incoming;
    std::map<vdisc, std::vector<edisc> > adjacent_outgoing;

    std::map<edisc, std::pair<vdisc, vdisc> > edgeVals;
    std::map<edisc, Edge> edgeNames;
    std::map<vdisc, Node> vertNames;

  public:
    edisc addEdge(const vdisc s, const vdisc e) {
      edisc ed = nextEdgeDisc();

      edges.push_back(ed);
      edgeVals.insert({ed, {s, e}});

      map_insert(adjacent_outgoing, s, ed);
      map_insert(adjacent_incoming, e, ed);

      return ed;
    }

    vdisc addVertex(const Node& w) {
      assert(w.isOpNode());

      vdisc v = nextVertexDisc();
      verts.push_back(v);
      vertNames[v] = w;
      return v;
    }

    void addVertex(const vdisc v) {
      assert(!elem(v, verts));

      verts.push_back(v);
    }

    vdisc addVertex() {
      vdisc v = nextVertexDisc();
      verts.push_back(v);
      return v;
    }

    void addVertLabel(const vdisc vd, const WireNode& wd) {
      vertNames.erase(vd);

      vertNames.insert({vd, wd});

    }

    void addEdgeLabel(const edisc ed, const Conn& conn) {

      edgeNames[ed] = conn;

    }

    edisc nextEdgeDisc() const {
      return edges.size();
    }

    vdisc nextVertexDisc() const {
      return verts.size();
    }
    
  };
  
  class NGraph {
  protected:
    DirectedGraph<WireNode, Conn> g;
    
    std::vector<edisc> edges;
    std::vector<vdisc> verts;

    std::map<vdisc, std::vector<edisc> > adjacent_incoming;
    std::map<vdisc, std::vector<edisc> > adjacent_outgoing;

    std::map<edisc, std::pair<vdisc, vdisc> > edgeVals;
    std::map<edisc, Conn> edgeNames;
    std::map<vdisc, WireNode> vertNames;


  public:
    WireNode getNode(const vdisc vd) const {
      auto vit = vertNames.find(vd);

      assert(vit != std::end(vertNames));

      return (*vit).second;
    }

    Conn getConn(const edisc ed) const {

      auto eit = edgeNames.find(ed);

      assert(eit != std::end(edgeNames));

      return (*eit).second;
    }

    bool hasLabel(const edisc ed) const;

    vdisc source(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.first;
    }

    void addVertLabel(const vdisc vd, const WireNode& wd) {
      vertNames.erase(vd);

      vertNames.insert({vd, wd});

    }

    void addEdgeLabel(const edisc ed, const Conn& conn) {

      edgeNames[ed] = conn;

    }

    vdisc target(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.second;
    }

    edisc addEdge(const vdisc s, const vdisc e) {
      edisc ed = nextEdgeDisc();

      edges.push_back(ed);
      edgeVals.insert({ed, {s, e}});

      map_insert(adjacent_outgoing, s, ed);
      map_insert(adjacent_incoming, e, ed);

      return ed;
    }

    edisc nextEdgeDisc() const {
      return edges.size();
    }

    vdisc nextVertexDisc() const {
      return verts.size();
    }
    
    vdisc addVertex(const WireNode& w) {
      assert(w.isOpNode());

      vdisc v = nextVertexDisc();
      verts.push_back(v);
      vertNames[v] = w;
      return v;
    }

    void addVertex(const vdisc v) {
      assert(!elem(v, verts));

      verts.push_back(v);
    }

    vdisc addVertex() {
      vdisc v = nextVertexDisc();
      verts.push_back(v);
      return v;
    }
    
    std::vector<edisc> outEdges(const vdisc vd) const {
      if (adjacent_outgoing.find(vd) == std::end(adjacent_outgoing)) {
	return {};
      }

      return map_find(vd, adjacent_outgoing);

    }

    std::vector<edisc> inEdges(const vdisc vd) const {
      if (adjacent_incoming.find(vd) == std::end(adjacent_incoming)) {
	return {};
      }

      return map_find(vd, adjacent_incoming);

    }

    std::vector<edisc> getEdges() const {
      return edges;
    }

    std::vector<vdisc> getVerts() const {
      return verts;
    }

    bool containsOpNode(CoreIR::Wireable* w) const {
      WireNode wn = combNode(w);

      for (auto& vpair : vertNames) {
	if (vpair.second == wn) {
	  return true;
	}
      }

      return false;
    }

    bool connected(const vdisc source, const vdisc dest) const {
      for (auto& ed : outEdges(source)) {
	if (target(ed) == dest) {
	  return true;
	}
      }

      return false;
    }

    vdisc getOpNodeDisc(CoreIR::Wireable* w) const {
      WireNode wn = combNode(w);

      for (auto& vpair : vertNames) {
	if (vpair.second == wn) {
	  return vpair.first;
	}
      }

      assert(false);
    }

    int numVertices() const;

    std::vector<vdisc> vertsWithNoIncomingEdge() const;
    std::vector<Conn> getInputConnections(const vdisc vd) const;
    std::vector<Conn> getOutputConnections(const vdisc vd) const;
    std::vector<CoreIR::Wireable*> getInputs(const vdisc vd) const;
    std::vector<CoreIR::Wireable*> getOutputs(const vdisc vd) const;
  };

  typedef NGraph NGraph;

  int numVertices(const NGraph& g);
  std::deque<vdisc> topologicalSort(const NGraph& g);

  std::vector<Conn> getInputConnections(const vdisc vd, const NGraph& g);
  std::vector<CoreIR::Wireable*> getInputs(const vdisc vd, const NGraph& g);
  std::vector<CoreIR::Wireable*> getOutputs(const vdisc vd, const NGraph& g);

  Conn getConn(const NGraph& g, const edisc ed);
  WireNode getNode(const NGraph& g, const vdisc vd);

  CoreIR::Wireable* extractSource(CoreIR::Select* sel);

  std::vector<Conn> getOutputConnections(const vdisc vd, const NGraph& g);

  void addWireableToGraph(CoreIR::Wireable* w1,
			  std::unordered_map<WireNode, vdisc>& imap,
			  NGraph& g);

  std::vector<Conn> buildOrderedConnections(Module* mod);

  void buildOrderedGraph(Module* mod, NGraph& g);

  InstanceValue findArg(std::string argName, std::vector<Conn>& ins);

  void eliminateMasks(const std::deque<vdisc>& topoOrder,
		      NGraph& g);

  int numMasksNeeded(const NGraph& g);

  std::vector<vdisc> vertsWithNoIncomingEdge(const NGraph& g);

  std::vector<std::vector<vdisc> > topologicalLevels(const NGraph& g);

  bool isThreadShared(const vdisc v, const NGraph& g);

  Select* findMainClock(const NGraph& g);

  bool isSubgraphInput(const vdisc vd,
                       const std::deque<vdisc>& nodes,
                       const NGraph& g);

  bool isSubgraphOutput(const vdisc vd,
                        const std::deque<vdisc>& nodes,
                        const NGraph& g);
  
  bool subgraphHasCombinationalInput(const std::deque<vdisc>& nodes,
                                     const NGraph& g);

  bool subgraphHasAllSequentialOutputs(const std::deque<vdisc>& nodes,
                                       const NGraph& g);

  bool subgraphHasAllSequentialInputs(const std::deque<vdisc>& nodes,
                                      const NGraph& g);

  bool subgraphHasCombinationalOutput(const std::deque<vdisc>& nodes,
                                      const NGraph& g);

  bool subgraphHasSequentialInput(const std::deque<vdisc>& nodes,
                                  const NGraph& g);

  bool subgraphHasSequentialOutput(const std::deque<vdisc>& nodes,
                                   const NGraph& g);

  bool subgraphHasAllCombinationalInputs(const std::deque<vdisc>& nodes,
                                         const NGraph& g);

  bool subgraphHasAllCombinationalOutputs(const std::deque<vdisc>& nodes,
                                          const NGraph& g);

  bool isConstant(const WireNode& wd);
}
