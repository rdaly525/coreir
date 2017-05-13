#ifndef DIRECTEDVIEW_HPP_
#define DIRECTEDVIEW_HPP_

#include "common.hpp"

//This is so that you can view a module graph as an instance view
namespace CoreIR {

class DirectedConnection;
class DirectedModule;
class DirectedInstance;
typedef std::vector<DirectedConnection> DirectedConnections;
typedef std::vector<DirectedInstance> DirectedInstances;

class DirectedConnection {
  Connection c;

  Wireable* src;
  Wireable* snk;
  public:
    DirectedConnection(Connection& c);
    SelectPath getSrc();
    SelectPath getSnk();
    Context* getContext();
    Connection operator->() {return c;}
};

class DirectedModule {
  //Reference Module
  Module* m;
  
  //unordered list of edges
  DirectedConnections connections;

  //Unordered list of all instances
  DirectedInstances insts;
  
  DirectedConnections inputs;
  DirectedConnections outputs;

  public:
    DirectedModule(Module* m);
    Wireable* sel(SelectPath path);
    DirectedConnections getConnections() { return connections;}
    DirectedInstances getInstances() { return insts;}
    DirectedConnections getInputs() { return inputs;}
    DirectedConnections getOutputs() { return outputs;}
    Context* getContext();
    Module* operator->() {return m;}
};


class DirectedInstance {
  //Reference instance
  Instance* i;
  
  //Input edges to this module
  DirectedConnections inputs;

  //Output edges from this module
  DirectedConnections outputs;

  public:
    DirectedInstance(Instance* i, DirectedConnections inputs, DirectedConnections outputs);
    DirectedConnections getInputs() {return inputs;}
    DirectedConnections getOutputs() {return outputs;}
    Instance* operator->() {return i;}

};

}//CoreIR

#endif //DIRECTEDVIEW_HPP_
