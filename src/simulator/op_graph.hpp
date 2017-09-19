#pragma once

#include "wire_node.hpp"

namespace CoreIR {

  typedef WireNode WireableNode;

  typedef std::pair<WireableNode, WireableNode> Conn;

  typedef int vdisc;
  typedef int edisc;

  class NGraph {
  protected:
    std::vector<edisc> edges;
    std::vector<vdisc> verts;

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

    vdisc source(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.first;
    }

    void addEdgeLabel(const edisc ed, const Conn& conn) {

      edgeNames[ed] = conn;

    }

    vdisc target(const edisc ed)  const {
      auto eit = edgeVals.find(ed);

      assert(eit != std::end(edgeVals));

      return (*eit).second.second;
    }

    edisc nextEdgeDisc() const {
      return edges.size();
    }

    vdisc nextVertexDisc() const {
      return verts.size();
    }
    
    edisc addEdge(const vdisc s, const vdisc e) {
      edisc ed = nextEdgeDisc();

      edges.push_back(ed);
      edgeVals.insert({ed, {s, e}});

      return ed;
    }

    vdisc addVertex(const WireNode& w) {
      assert(w.isOpNode());

      vdisc v = nextVertexDisc();
      verts.push_back(v);
      vertNames[v] = w;
      return v;
    }

    std::vector<edisc> outEdges(const vdisc vd) const {
      std::vector<edisc> eds;
      for (auto& e : edges) {
	if (source(e) == vd) {
	  eds.push_back(e);
	}
      }
      return eds;
    }

    std::vector<edisc> inEdges(const vdisc vd) const {
      std::vector<edisc> eds;
      for (auto& e : edges) {
	if (target(e) == vd) {
	  eds.push_back(e);
	}
      }
      return eds;
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

  int numVertices(const NGraph& g);
  std::deque<vdisc> topologicalSort(const NGraph& g);

  std::vector<Conn> getInputConnections(const vdisc vd, const NGraph& g);
  std::vector<CoreIR::Wireable*> getInputs(const vdisc vd, const NGraph& g);
  std::vector<CoreIR::Wireable*> getOutputs(const vdisc vd, const NGraph& g);

  Conn getConn(const NGraph& g, const edisc ed);
  WireNode getNode(const NGraph& g, const vdisc vd);

  CoreIR::Wireable* extractSource(CoreIR::Select* sel);

  std::vector<Conn> getOutputConnections(const vdisc vd, const NGraph& g);

  void addConnection(std::unordered_map<WireNode, vdisc>& imap,
		     Conn& conn,
		     NGraph& g);
  
  void addWireableToGraph(CoreIR::Wireable* w1,
			  std::unordered_map<WireNode, vdisc>& imap,
			  NGraph& g);

  std::vector<Conn> buildOrderedConnections(Module* mod);

  void buildOrderedGraph(Module* mod, NGraph& g);

  WireNode findArg(std::string argName, std::vector<Conn>& ins);

  void eliminateMasks(const std::deque<vdisc>& topoOrder,
		      const NGraph& g);

  int numMasksNeeded(const NGraph& g);

}
