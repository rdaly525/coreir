
#include "coreir.h"
#include "cxxopts.hpp"

#include "Vtop.h"
#include "verilated.h"

#include <fstream>

using namespace CoreIR;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

int main(int argc, char **argv, char **env) {
  int argc_copy = argc;
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("h,help","help")
    ("i,input","input file: <file>.raw",cxxopts::value<std::string>())
    ("o,output","output file: <file>.raw",cxxopts::value<std::string>())
    ("d,delay","pipeline delay",cxxopts::value<int>())
    ("n,nclocks","max clock cycles",cxxopts::value<int>())
    ;
  
  //Do the parsing of the arguments
  options.parse(argc,argv);
 
  if (options.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    exit(1);
  }

  ASSERT(options.count("i"),"No input specified")
  string infileName = options["i"].as<string>();
  ASSERT(getExt(infileName) == "raw",infileName + " is not raw");
  
  ASSERT(options.count("o"),"No output specified")
  string outfileName = options["o"].as<string>();
  ASSERT(getExt(outfileName) == "raw",outfileName + " is not raw");

  std::fstream ifile;
  ifile.open(infileName,ios::in | ios::binary);
  ASSERT(ifile.is_open(), infileName + " could not be opened");

  std::fstream ofile;
  ofile.open(outfileName, ios::out | ios::binary);
  ASSERT(ofile.is_open(), outfileName + " could not be opened");
  
  int delay = 0;
  if (options.count("d")) {
    delay = options["d"].as<int>();
  }

  int nclks = 40000;
  if (options.count("n")) {
    nclks = options["n"].as<int>();
  }

  Verilated::commandArgs(argc, argv);
  Vtop* top = new Vtop;

  top->clk = 0;
  top->eval();
  top->clk = 1;
  top->eval();

  for (int i=0; i<nclks; ++i) {
    top->clk = 0;
    uint16_t in=0;
    ifile.read((char*)&in,1);
    if (ifile.eof()) {
      cout << "i=" << i << endl;
      break;
    }
    top->in_0 = in;
    //cout << "in: " << in << endl;
 
    top->eval();
    //negedge ---------------
    
    if (i >=delay) {
      uint16_t out = top->out & 0xff;
      //cout << "out: " << out << endl;
      ofile.write((char*)&out,1);
    }

    top->clk = 1;
    
    
    top->eval();
    //posedge ---------------
  }

  top->in_0 = 0; //Dont care
  for (int i=0; i<delay; ++i) {
    top->clk = 0;
    top->eval();
    //negedge ---------------
    uint16_t out = top->out;
    ofile.write((char*)&out,1);
    
    top->clk = 1;
    top->eval();
    //posedge ---------------

  }
  ifile.close();
  ofile.close();

} 
