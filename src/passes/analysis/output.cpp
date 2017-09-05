#include "output.hpp"

#include <fstream>
#include <iostream>

#include "sim.hpp"

using namespace std;

namespace CoreIR {

  int compileCode(const std::string& code, const std::string& outFile) {
    std::ofstream out(outFile);
    out << code;
    out.close();


    string runCmd = "clang -c " + outFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    return s;

  }

  void writeFiles(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& codeFile,
		  const std::string& hFile) {
    string codeStr = printCode(topoOrder, g, mod);
    string hStr = printDecl(mod);

    std::ofstream out(codeFile);
    out << codeStr;
    out.close();

    std::ofstream outH(hFile);
    outH << hStr;
    outH.close();

  }

  int compileCodeAndRun(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			Module* mod,
			const std::string& outFile,
			const std::string& harnessFile) {

    string hFile = outFile + ".h";
    string codeFile = outFile + ".c";

    writeFiles(topoOrder, g, mod, codeFile, hFile);
  
    string runCmd = "clang " + codeFile + " " + harnessFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    string runTest = "./a.out";
    int r = system(runTest.c_str());

    cout << "Test result = " << r << endl;

    return s || r;
  }

  int compileCodeAndRun(const std::string& code,
			const std::string& outFile,
			const std::string& harnessFile) {
    std::ofstream out(outFile);
    out << code;
    out.close();

    string runCmd = "clang " + outFile + " " + harnessFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    //return s;

    string runTest = "./a.out";
    int r = system(runTest.c_str());

    cout << "Test result = " << r << endl;

    return s || r;
  }  
  
}
