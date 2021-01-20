#include <fstream>
#include <stdlib.h>
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/passes/analysis/verilog.h"

using namespace CoreIR;

namespace {

const char* kExpectedFilenames[] = {"corebit_not.v",
                                    "corebit_and.v",
                                    "SplitFilesTop.v"};
const int kNumExpectedFiles = 3;

class SplitFilesFixture {
 public:
  SplitFilesFixture(std::string infile)
      : context_(newContext()),
        top_(nullptr) {
    Init(infile);
  }

  Passes::Verilog* RunVerilogPass() {
    context_->runPasses(
      {"rungenerators", "removebulkconnections", "flattentypes", "verilog"},
      {"global"});
    return static_cast<Passes::Verilog*>(
      context_->getPassManager()->getAnalysisPass("verilog"));
  }

 private:
  void Init(std::string infile) {
    const auto load_res = loadFromFile(
      context_.get(),
      "split_files_in.json",
      &top_);
    ASSERT(load_res, "Could not load split_files_in.json");
    ASSERT(top_, "Top module not present");
    context_->setTop(top_->getRefName());
    CoreIRLoadVerilog_coreir(context_.get());
    CoreIRLoadVerilog_corebit(context_.get());
  }

  std::unique_ptr<Context> context_;
  Module* top_;
};

bool FileExists(std::string filename) {
  // This is not the best check but is passable.
  // TODO(rsetaluri): Make this function robust and resuable.
  std::ifstream file(filename);
  return file.good();
}

}  // namespace

void TestSplitFiles() {
  SplitFilesFixture fixture("split_files_in.json");
  auto verilog_pass = fixture.RunVerilogPass();
  verilog_pass->writeToFiles("./", {}, "v");
  for (int i = 0; i < kNumExpectedFiles; i++) {
    const std::string expected = std::string(kExpectedFilenames[i]);
    ASSERT(FileExists(expected), "File '" + expected + "' does not exist");
  }
}

void TestProductList() {
  SplitFilesFixture fixture("split_files_in.json");
  auto verilog_pass = fixture.RunVerilogPass();
  std::unique_ptr<std::string> product_file(new std::string("product.txt"));
  verilog_pass->writeToFiles("./", std::move(product_file), "v");
  std::ifstream infile("product.txt");
  std::string filename;
  for (int i = 0; i < kNumExpectedFiles; i++) {
    ASSERT(infile >> filename, "Expected more lines in product.txt");
    const std::string expected = std::string(kExpectedFilenames[i]);
    ASSERT(FileExists(expected), "File '" + expected + "' does not exist");
    ASSERT(
      expected == filename,
      "Expected '" + expected + "', got '" + filename + "'");
  }
}

int main() { TestSplitFiles(); }
