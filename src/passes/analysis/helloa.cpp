
using namespace CoreIR;

Passes::HelloA::runOnNamespace(Namespace* ns) {
  cout << "Running HelloA" << endl;
  this->str = "HelloATester";
}
