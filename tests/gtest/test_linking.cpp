#include <gtest/gtest.h>
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/ir/context.h"

using namespace CoreIR;

//std::string base = "../../tests/gtest/";
std::string base = ".";
std::string app_file = base + "/srcs/linking_app.json";
std::string header_file = base + "/srcs/linking_header.json";
std::string impl_file = base + "/srcs/linking_impl.json";

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
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);

}

// Same setup as header test, but also have an implementation of that header as a json file
TEST(LinkingTest, LinkImpl) {

  std::string build_file = base + "/build/linking_LinkImpl.json";
  std::string golden_file = base + "/golds/linking_LinkImpl.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkDefinitions(c, impl_file)) {c->die();}

  Module* top;
  if (!loadFromFile(c, app_file, &top)) {c->die();}
  c->setTop(top);

  serializeToFile(c, build_file);
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}

// Load a header, and save a header
TEST(LinkingTest, HeaderGen1) {
  std::string build_file = base + "/build/linking_HeaderGen1.json";
  std::string golden_file = base + "/golds/linking_HeaderGen1.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}

  serializeHeader(c, build_file, {"global.A", "global.B", "global.C"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}

// Load a header and impl, then save impl
TEST(LinkingTest, HeaderGen2) {
  std::string build_file = base + "/build/linking_HeaderGen2.json";
  std::string golden_file = base + "/golds/linking_HeaderGen2.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkDefinitions(c, impl_file)) {c->die();}

  serializeHeader(c, build_file, {"global.A", "global.B", "global.C"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}

//Same as above test, but loads the app before creating the header
TEST(LinkingTest, HeaderGen3) {
  std::string build_file = base + "/build/linking_HeaderGen3.json";
  std::string golden_file = base + "/golds/linking_HeaderGen3.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkDefinitions(c, impl_file)) {c->die();}

  Module* top;
  if (!loadFromFile(c, app_file, &top)) {c->die();}
  c->setTop(top);

  serializeHeader(c, build_file, {"global.A", "global.B", "global.C"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}


//Impl generator tests.

// Load a header, save impl
TEST(LinkingTest, ImplGen1) {
  std::string build_file = base + "/build/linking_ImplGen1.json";
  std::string golden_file = base + "/golds/linking_ImplGen1.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}

  serializeDefinitions(c, build_file, {"global.A", "global.B"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}

TEST(LinkingTest, ImplGen2) {
  std::string build_file = base + "/build/linking_ImplGen2.json";
  std::string golden_file = base + "/golds/linking_ImplGen2.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkDefinitions(c, impl_file)) {c->die();}

  serializeDefinitions(c, build_file, {"global.A", "global.B"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}

//Same as above test, but loads the app before generating the impl
TEST(LinkingTest, ImplGen3) {
  std::string build_file = base + "/build/linking_ImplGen3.json";
  std::string golden_file = base + "/golds/linking_ImplGen3.json";

  auto c = newContext();
  vector<Module*> loaded;
  if (!loadHeader(c, header_file, loaded)) {c->die();}
  if (!linkDefinitions(c, impl_file)) {c->die();}

  Module* top;
  if (!loadFromFile(c, app_file, &top)) {c->die();}
  c->setTop(top);

  serializeDefinitions(c, build_file, {"global.A", "global.B"});
  validCoreIR(build_file);
  assertFileEq(build_file, golden_file);
}


int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
