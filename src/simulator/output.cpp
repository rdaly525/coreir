#include "output.hpp"

#include <fstream>
#include <iostream>

#include "sim.hpp"
#include "bsim_lib.hpp"

using namespace std;

namespace CoreIR {

  void writeBitVectorLib(const std::string& path) {
    string libText = blib();

    std::ofstream out(path);
    out << libText;
    out.close();
  }
  
  void writeBitVectorLib() {
    writeBitVectorLib("./gencode/bit_vector.h");
  }

  int compileCode(const std::string& code, const std::string& outFile) {

    writeBitVectorLib();
    std::ofstream out(outFile);
    out << code;
    out.close();

    string runCmd = "clang++ -lpthread -std=c++11 -c " + outFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    return s;

  }

  void writeFiles(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& codePath,
		  const std::string& codeFile,
		  const std::string& hFile) {

    string codeStr = printCode(topoOrder, g, mod, hFile);
    string hStr = printDecl(mod, g);

    string codeFilePath = codePath + codeFile;
    string hFilePath = codePath + hFile;

    std::ofstream out(codeFilePath);
    out << codeStr;
    out.close();

    std::ofstream outH(hFilePath);
    outH << hStr;
    outH.close();

  }

  void writeFiles(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& codeFile,
		  const std::string& hFile) {

    string codeStr = printCode(topoOrder, g, mod, hFile);
    string hStr = printDecl(mod, g);

    std::ofstream out(codeFile);
    out << codeStr;
    out.close();

    std::ofstream outH(hFile);
    outH << hStr;
    outH.close();

  }
  
  int compileCode(const std::deque<vdisc>& topoOrder,
		  NGraph& g,
		  Module* mod,
		  const std::string& outDir,
		  const std::string& baseFileName) {
    writeBitVectorLib();    

    string hFile = baseFileName + ".h";
    string codeFile = baseFileName + ".cpp";

    writeFiles(topoOrder, g, mod, outDir, codeFile, hFile);

    string codeFilePath = outDir + codeFile;
  
    string runCmd = "clang++ -lpthread -std=c++11 -c " + codeFilePath;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    return s;
  }  

  int compileCodeAndRun(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			Module* mod,
			const std::string& outDir,
			const std::string& baseFileName,
			const std::string& harnessFile) {

    writeBitVectorLib();    

    string hFile = baseFileName + ".h";
    string codeFile = baseFileName + ".cpp";

    writeFiles(topoOrder, g, mod, outDir, codeFile, hFile);

    string codeFilePath = outDir + codeFile;

    string harnessFilePath = outDir + harnessFile;
    string runCmd = "clang++ -lpthread -std=c++11 " + codeFilePath + " " + harnessFilePath;
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

    writeBitVectorLib();
    
    std::ofstream out(outFile);
    out << code;
    out.close();

    string runCmd = "clang++ -lpthread -std=c++11 " + outFile + " " + harnessFile;
    int s = system(runCmd.c_str());

    cout << "Command result = " << s << endl;

    //return s;

    string runTest = "./a.out";
    int r = system(runTest.c_str());

    cout << "Test result = " << r << endl;

    return s || r;
  }  

}
