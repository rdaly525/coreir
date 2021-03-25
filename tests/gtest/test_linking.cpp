#include <gtest/gtest.h>
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/ir/context.h"

using namespace CoreIR;

std::string base = "../../tests/gtest/";
std::string app_file = base + "srcs/linking_app.json";
std::string header_file = base + "srcs/linking_header.json";
std::string impl_file = base + "srcs/linking_impl.json";

TEST(LinkingTest, HeaderLoad) {
  std::string build_file = base + "/build/linking_HeaderLoad.json";
  std::string golden_file = base + "/golds/linking_HeaderLoad.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  ASSERT_TRUE(loaded.size()==3);
  ASSERT_TRUE(loaded[0]->getRefName() == "global.A");
  ASSERT_TRUE(loaded[1]->getRefName() == "global.B");
  ASSERT_TRUE(loaded[2]->getRefName() == "global.C");

  Module* top;
  if (!loadFromFile(c, app_file, &top)) {c->die();}
  c->setTop(top);

  serializeToFile(c, build_file);

  assertFileEq(build_file, golden_file);

}

//TODO Ross Start here. Fill in a basic impl file for A and B (have A depend on C)
// Same setup as header test, but also have an implementation of that header as a json file
TEST(LinkingTest, LinkImpl) {

  std::string build_file = base + "/build/linking_LinkImpl.json";
  std::string golden_file = base + "/golds/linking_LinkImpl.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkImpl(c, impl_file)) {c->die();}

  Module* top;
  if (!loadFromFile(c, app_file, &top)) {c->die();}
  c->setTop(top);

  serializeToFile(c, build_file);
  assertFileEq(build_file, golden_file);
}


// Given Module(s), save as a header file (with no definition) “Unlink”
TEST(LinkingTest, HeaderGen1) {
  std::string header_gen_file = "../../tests/gtest/build/linking_header_gen1.json";
  std::string golden_file = "../../tests/gtest/gold/linking_header_gen1.json";
  auto c = newContext();
  if (!loadFromFile(c, header_file)) {c->die();}
  saveHeader(c, header_gen_file, {"global.A", "global.B", "global.C"});
  assertFileEq(header_gen_file, golden_file);
}


// Given Module(s), save as a header file (with no definition) “Unlink”
TEST(LinkingTest, HeaderGen2) {
  std::string header_gen_file = "../../tests/gtest/build/linking_header_gen1.json";
  std::string golden_file = "../../tests/gtest/gold/linking_header_gen1.json";
  auto c = newContext();
  if (!loadFromFile(c, header_file)) {c->die();}
  saveHeader(c, header_gen_file, {"global.A", "global.B", "global.C"});
  assertFileEq(header_gen_file, golden_file);
}

// Given Module(s), save an impl file with all definitions “Unlink”
TEST(LinkingTest, ImplGen) {
  auto c = newContext();
  if (!loadFromFile(c, impl_file)) {c->die();}

}


int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
