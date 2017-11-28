
#include "coreir.h"
#include "cxxopts.hpp"

#include <fstream>

using namespace CoreIR;
using namespace std;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

void checkRange(int val, int lo, int hi) {
  ASSERT(val >= lo && val <= hi,"Needs to be: " + to_string(lo) + "<=" + to_string(val) + "<=" + to_string(hi));
}

int fileSizeBytes(fstream& f) {
  f.seekg(0,std::ios_base::end);
  int ret = f.tellg();
  f.seekg(0,std::ios_base::beg);
  return ret;
}

int main(int argc, char **argv, char **env) {
  int argc_copy = argc;
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("h,help","help")
    ("i,input","input file: <file>.raw",cxxopts::value<std::string>())
    ("o,output","output file: <file>.raw",cxxopts::value<std::string>())
    ("d,delay","pipeline delay",cxxopts::value<int>())
    ("s,size","size: width,height",cxxopts::value<string>())
    ("c,cull","cull: ymin,ymax,xmin,xmax",cxxopts::value<string>())
    ;
  
  //Do the parsing of the arguments
  options.parse(argc,argv);
 
  if (options.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    exit(1);
  }

  int delay = 0;
  if (options.count("d")) {
    delay = options["d"].as<int>();
  }
  
  int H;
  int W;
  ASSERT(options.count("s"),"No size specified");
  auto sp = splitString<vector<string>>(options["s"].as<string>(),',');
  ASSERT(sp.size()==2,"bad size: " + options["s"].as<string>());
  H = stoi(sp[0]);
  W = stoi(sp[1]);

  int y0 = 0;
  int y1 = H;
  int x0 = 0;
  int x1 = W;
  ASSERT(options.count("s"),"No size specified");
  if (options.count("c")) {
    auto sp = splitString<vector<string>>(options["c"].as<string>(),',');
    ASSERT(sp.size()==4,"bad cull: " + options["c"].as<string>());
    y0 = stoi(sp[0]);
    y1 = stoi(sp[1]);
    x0 = stoi(sp[2]);
    x1 = stoi(sp[3]);
  }
  checkRange(x0,0,W);
  checkRange(y0,0,H);
  checkRange(x1,x0,W);
  checkRange(y1,y1,H);

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
  

  //Check if h,w,x*,y* are all possible
  int size = fileSizeBytes(ifile);
  ASSERT(size > delay, "Size must be larger than delay: size=" + to_string(size) + " delay=" + to_string(delay) + "\n");
  ASSERT(delay >= 0, "delay must be non-negative");
  size = size-delay;

  ASSERT(W*H==size,to_string(W) + "*" + to_string(H) + "!=" + to_string(size));
  char c;
  for (int d=0; d<delay; d++) {
    ifile.read(&c,1);
  }
  for (int h=0; h<H; h++) {
    for (int w=0; w<W; w++) {
      ifile.read(&c,1);
      if (y0 <= h && h < y1 && x0 <=w && w<x1) {
        ofile.write(&c,1);
      }
    }
  }
  int osize = fileSizeBytes(ofile);
  cout << x1 << " " << x0 << " " << y1 << " " << y0 << endl;
  ASSERT(fileSizeBytes(ofile) == (x1-x0)*(y1-y0),"Bad!! "+ to_string(osize));

  ifile.close();
  ofile.close();

} 
