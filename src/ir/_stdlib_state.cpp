/////////////////////////////////
// Stdlib stateful primitives
//   reg, ram, rom
/////////////////////////////////

using namespace std;
using namespace CoreIR;

void stdlib_state(Context* c, Namespace* stdlib) {
  
  //Template
  /* Name: 
   * GenParams: 
   *    <Argname>: <Argtype>, <description>
   * Type: 
   * Fun: 
   * Argchecks: 
   */
   
  /* Name: reg
   * GenParams: 
   *    regType: TYPE, Type of register
   *    en: BOOL, has enable?
   *    clr: BOOL, has clr port
   *    rst: BOOL, has asynchronous reset
   * ConfigParams
   *    resetval: UINT, value at reset
   * Type: {'in':regType
   * Fun: out <= (rst|clr) ? resetval : en ? in : out;
   * Argchecks: 
   */
  auto regFun = [](Context* c, Args args) { 
    uint width = args.at("width")->get<ArgInt>();
    bool en = args.at("en")->get<ArgBool>();
    bool clr = args.at("clr")->get<ArgBool>();
    bool rst = args.at("rst")->get<ArgBool>();
    assert(!(clr && rst));

    RecordParams r({
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(width)}
    });
    if (en) r.push_back({"en",c->BitIn()});
    if (clr) r.push_back({"clr",c->BitIn()});
    if (rst) r.push_back({"rst",c->BitIn()});
    return c->Record(r);
  };
  Params regGenParams({
    {"width",AINT},
    {"en",ABOOL},
    {"clr",ABOOL},
    {"rst",ABOOL}
  });
  Params regConfigParams({{"init",AINT}});
  TypeGen* regTypeGen = stdlib->newTypeGen("regType",regGenParams,regFun);
  auto reg = stdlib->newGeneratorDecl("reg",regTypeGen,regGenParams,regConfigParams);
  reg->setDefaultGenArgs({{"en",c->argBool(false)},{"clr",c->argBool(false)},{"rst",c->argBool(false)}});
  reg->setDefaultConfigArgs({{"init",c->argInt(0)}});
}
