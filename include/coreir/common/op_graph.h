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

    int numVertices() const { return verts.size(); }

    std::map<vdisc, Node> getVertNames() const { return vertNames; }

    Node getNode(const vdisc vd) const {
      auto vit = vertNames.find(vd);

      assert(vit != std::end(vertNames));

      return (*vit).second;
    }

    Conn getConn(const edisc ed) const {

      auto eit = edgeNames.find(ed);

      assert(eit != std::end(edgeNames));

      return (*eit).second;
    }

    bool hasLabel(const edisc ed) const {
      return edgeNames.find(ed) != std::end(edgeNames);
    }

    vdisc target(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.second;
    }

    vdisc source(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.first;
    }

    std::vector<edisc> getEdges() const {
      return edges;
    }

    std::vector<vdisc> getVerts() const {
      return verts;
    }
    
    edisc addEdge(const vdisc s, const vdisc e) {
      edisc ed = nextEdgeDisc();

      edges.push_back(ed);
      edgeVals.insert({ed, {s, e}});

      map_insert(adjacent_outgoing, s, ed);
      map_insert(adjacent_incoming, e, ed);

      return ed;
    }

    vdisc addVertex(const Node& w) {
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

    bool connected(const vdisc source, const vdisc dest) const {

      for (auto& ed : outEdges(source)) {
        if (target(ed) == dest) {
          return true;
        }
      }

      return false;
    }

    std::vector<vdisc> vertsWithNoIncomingEdge() const {
      std::vector<vdisc> vs;
      for (auto v : getVerts()) {

        //if (getInputConnections(v).size() == 0) {
        if (inEdges(v).size() == 0) {
          vs.push_back(v);
        }
      }

      return vs;
    
    }
    
  };

  template<typename Node, typename Edge>
  std::vector<vdisc>
  vertsWithNoIncomingEdge(const DirectedGraph<Node, Edge>& g) {
    return g.vertsWithNoIncomingEdge();
  }

  template<typename Node, typename Edge>
  std::deque<vdisc> topologicalSort(const DirectedGraph<Node, Edge>& g) {
    std::deque<vdisc> topo_order;

    std::vector<vdisc> s = vertsWithNoIncomingEdge(g);

    //vector<edisc> deleted_edges;
    std::unordered_set<edisc> deleted_edges;

    //cout << "Starting topological sort" << endl;

    while (s.size() > 0) {
      vdisc vd = s.back();

      //assert(!elem(vd, topo_order));

      topo_order.push_back(vd);
      s.pop_back();

      
      for (auto ed : g.outEdges(vd)) {

	//deleted_edges.push_back(ed);
	deleted_edges.insert(ed);
	
	vdisc src = g.source(ed);
	vdisc dest = g.target(ed);

	assert(src == vd);

	bool noOtherEdges = true;

	for (auto in_ed : g.inEdges(dest)) {

	  if (!elem(in_ed, deleted_edges)) {
	    noOtherEdges = false;
	    break;
	  }
	}

	if (noOtherEdges){

	  //assert(!elem(dest, s));

	  s.push_back(dest);
	}
      }


    }

    // cout << "topo_order.size() = " << topo_order.size() << endl;
    // cout << "numVertices(g)    = " << numVertices(g) << endl;

    // cout << "Topological order" << endl;
    // for (auto& vd : topo_order) {
    //   cout << vd << endl;
    // }


    assert(topo_order.size() == (uint) g.numVertices());

    return topo_order;
    
  }
  
  class NGraph {
  protected:
    DirectedGraph<WireNode, Conn> g;
    
  public:
    WireNode getNode(const vdisc vd) const {
      return g.getNode(vd);
    }

    Conn getConn(const edisc ed) const {
      return g.getConn(ed);
    }

    bool hasLabel(const edisc ed) const {
      return g.hasLabel(ed);
    }

    vdisc source(const edisc ed)  const {
      return g.source(ed);
    }

    void addVertLabel(const vdisc vd, const WireNode& wd) {
      g.addVertLabel(vd, wd);
    }

    void addEdgeLabel(const edisc ed, const Conn& conn) {
      g.addEdgeLabel(ed, conn);
    }

    vdisc target(const edisc ed)  const {
      return g.target(ed);
    }

    edisc addEdge(const vdisc s, const vdisc e) {
      return g.addEdge(s, e);
    }

    edisc nextEdgeDisc() const {
      return g.nextEdgeDisc();
    }

    vdisc nextVertexDisc() const {
      return g.nextVertexDisc();
    }
    
    vdisc addVertex(const WireNode& w) {
      assert(w.isOpNode());

      return g.addVertex(w);
    }

    void addVertex(const vdisc v) {
      g.addVertex(v);

    }

    vdisc addVertex() {
      return g.addVertex();
    }
    
    std::vector<edisc> outEdges(const vdisc vd) const {
      return g.outEdges(vd);
    }

    std::vector<edisc> inEdges(const vdisc vd) const {
      return g.inEdges(vd);
    }

    std::vector<edisc> getEdges() const {
      return g.getEdges();
    }

    std::vector<vdisc> getVerts() const {
      return g.getVerts();
    }

    bool containsOpNode(CoreIR::Wireable* w) const {
      WireNode wn = combNode(w);

      for (auto& vpair : g.getVertNames()) {
	if (vpair.second == wn) {
	  return true;
	}
      }

      return false;
    }

    bool connected(const vdisc source, const vdisc dest) const {
      return g.connected(source, dest);
    }

    vdisc getOpNodeDisc(CoreIR::Wireable* w) const {
      WireNode wn = combNode(w);

      for (auto& vpair : g.getVertNames()) {
	if (vpair.second == wn) {
	  return vpair.first;
	}
      }

      assert(false);
    }

    int numVertices() const { return g.numVertices(); }

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

  std::deque<vdisc> topologicalSortNoFail(const NGraph& g);

}
