#include "gtest/gtest.h"
#include "assert_pass.h"
#include "coreir.h"
#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/libs/commonlib.h"

using namespace CoreIR;

namespace {

TEST(UnitTests, AnyTest) {
  Json jdata;
  jdata["mylist"][0] = 5;
  jdata["mylist"][1] = "string";
  jdata["mylist"][2] = {{"a", 13}, {"b", 2}};

  {
    Context* c = newContext();


    Values g5 = {{"a", Const::make(c, jdata)}};
    checkValuesAreParams(g5, {{"a", JsonType::make(c)}});
    cout << "jsonval: " << jdata << endl;
    cout << "jsonval2: " << g5.at("a")->get<Json>() << endl;

    Namespace* g = c->getGlobal();

    // Declare a TypeGenerator (in global) for addN
    g->newTypeGen(
      "json_type",  // name for the typegen
      {{"width", c->Any()}},
      [](Context* c, Values args) {  // Function to compute type
        Json width = args.at("width")->get<Json>();
        return c->Record({{"in",
                           c->BitIn()
                             ->Arr(width["mylist"][0])
                             ->Arr(width.at("mylist")[2].at("a"))},
                          {"out", c->Bit()->Arr(3)}});
      });

    g->newGeneratorDecl(
      "addN",
      g->getTypeGen("json_type"),
      {{"width", c->Any()}});

    Module* top = g->newModuleDecl("top", c->Record());
    ModuleDef* def = top->newModuleDef();
    def->addInstance("inst", "global.addN", {{"width", Const::make(c, jdata)}});
    top->setDef(def);

    if (!saveToFile(g, "_anytest.json", top)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    deleteContext(c);
  }
  {
    auto c = newContext();
    if (!loadFromFile(c, "_anytest.json")) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }
    auto top = c->getModule("global.top");
    ASSERT_TRUE(top->hasDef());
    auto top_def = top->getDef();
    auto insts = top_def->getInstances();
    auto inst = insts.at("inst");
    auto mref = inst->getModuleRef();
    auto genargs = mref->getGenArgs();
    auto width_arg = genargs.at("width");
    auto width = width_arg->get<Json>();

    ASSERT_TRUE(jdata == width);
    deleteContext(c);
  }
}

TEST(UnitTests, SaveAndLoad) {
  std::string file1 = "build/_add12.json";
  std::string file2 = "build/_add12Gen.json";
  {
    // New context
    Context* c = newContext();

    // Put this addN in the global namespace
    Namespace* g = c->getGlobal();

    // Declare a TypeGenerator (in global) for addN
    g->newTypeGen(
      "addN_type",                             // name for the typegen
      {{"width", c->Int()}, {"N", c->Int()}},  // generater parameters
      [](Context* c, Values args) {            // Function to compute type
        uint width = args.at("width")->get<int>();
        uint N = args.at("N")->get<int>();
        return c->Record({{"in", c->BitIn()->Arr(width)->Arr(N)},
                          {"out", c->Bit()->Arr(width)}});
      });

    Generator* addN = g->newGeneratorDecl(
      "addN",
      g->getTypeGen("addN_type"),
      {{"width", c->Int()}, {"N", c->Int()}});

    addN->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("width")->get<int>();
      uint N = args.at("N")->get<int>();
      assert((N & (N - 1)) == 0);  // Check if power of 2
      assert(N != 1);

      Namespace* coreir = c->getNamespace("coreir");
      Generator* add2 = coreir->getGenerator("add");
      Generator* addN = c->getGlobal()->getGenerator("addN");

      Value* aWidth = Const::make(c, width);

      def->addInstance("join", add2, {{"width", aWidth}});
      def->connect("join.out", "self.out");

      if (N == 2) {
        def->connect("self.in.0", "join.in0");
        def->connect("self.in.1", "join.in1");
      }
      else {
        // Connect half instances
        Value* aN2 = Const::make(c, N / 2);
        def->addInstance("addN_0", addN, {{"width", aWidth}, {"N", aN2}});
        def->addInstance("addN_1", addN, {{"width", aWidth}, {"N", aN2}});
        for (uint i = 0; i < N / 2; ++i) {
          def->connect(
            {"self", "in", to_string(i)},
            {"addN_0", "in", to_string(i)});
          def->connect(
            {"self", "in", to_string(i + N / 2)},
            {"addN_1", "in", to_string(i)});
        }
        def->connect("addN_0.out", "join.in0");
        def->connect("addN_1.out", "join.in1");
      }
    });

    // Define Add12 Module
    Type* add12Type = c->Record({{"in8", c->BitIn()->Arr(13)->Arr(8)},
                                 {"in4", c->BitIn()->Arr(13)->Arr(4)},
                                 {"out", c->Bit()->Arr(13)}});

    Namespace* coreir = c->getNamespace("coreir");
    Module* add12 = g->newModuleDecl("Add12", add12Type);
    ModuleDef* def = add12->newModuleDef();
    def->addInstance(
      "add8_upper",
      addN,
      {{"width", Const::make(c, 13)}, {"N", Const::make(c, 8)}});
    def->addInstance(
      "add4_lower",
      addN,
      {{"width", Const::make(c, 13)}, {"N", Const::make(c, 4)}});
    def->addInstance(
      "add2_join",
      coreir->getGenerator("add"),
      {{"width", Const::make(c, 13)}});
    def->connect("self.in8", "add8_upper.in");
    def->connect("self.in4", "add4_lower.in");
    def->connect("add8_upper.out", "add2_join.in0");
    def->connect("add4_lower.out", "add2_join.in1");
    def->connect("add2_join.out", "self.out");
    add12->setDef(def);

    cout << "Checking saving and loading pregen" << endl;
    if (!saveToFile(g, file1, add12)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    deleteContext(c);
  }
  {
    auto c = newContext();
    auto g = c->getGlobal();

    cout << "loading" << endl;
    if (!loadFromFile(c, file1)) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }
    auto add12 = c->getModule("global.Add12");
    add12->getDef()->validate();

    cout << "Checking saving and loading postgen" << endl;
    if (!saveToFile(g, file2, add12)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }
    deleteContext(c);
  }
  {
    auto c = newContext();
    Module* m = nullptr;
    if (!loadFromFile(c, file2, &m)) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }
    ASSERT(m, "Could not load top: add12");
    deleteContext(c);
  }
}


}  // namespace

int main(int argc, char** argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
