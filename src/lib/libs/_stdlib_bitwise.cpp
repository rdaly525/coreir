/////////////////////////////////
// Stdlib Bitwise primitives
//   not,and,or,xor,andr,orr,xorr
/////////////////////////////////

inline void stdlib_bitwise(Context* c, Namespace* stdlib) {
  
  //Template
  /* Name: 
   * GenParams: 
   *    <Argname>: <Argtype>, <description>
   * Type: 
   * Fun: 
   * Argchecks: 
   */
  
  Params widthparam = Params({{"width",UINT}});

  auto bitwiseA2AFun = [](Context* c, Args args) { 
    uint width = args.at("width");
    return c->Record({
        {"in",c->Array(width,c->BitIn())},
        {"out",c->Array(width,c->BitOut())}
    });
  } 
  auto bitwiseA2A2AFun = [](Context* c, Args args) { 
    uint width = args.at("width");
    return c->Record({
        {"in",c->Array(2,c->Array(width,c->BitIn()))},
        {"out",c->Array(width,c->BitOut())}
    });
  } 
  auto bitwiseA2BitFun = [](Context* c, Args args) { 
    uint width = args.at("width");
    return c->Record({
        {"in",c->Array(width,c->BitIn())},
        {"out",c->BitOut()}
    });
  } 
  
  /* Name: not
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitOut[width]
   * Fun: out = ~in
   * Argchecks: 
   */
  auto notFun = bitwiseA2AFun;
  Params notParams = widthparam;
  TypeGen notTypeGen(notParams,notFun);
  stdlib->newGeneratorDecl("not",notParams,notTypeGen);
  
  /* Name: and
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> BitOut[width]
   * Fun: out = in[0] & in[1]
   * Argchecks: 
   */
  auto andFun = bitwiseA2A2AFun;
  Params andParams = widthparam;
  TypeGen andTypeGen(andParams,andFun);
  stdlib->newGeneratorDecl("and",andParams,andTypeGen);
  
  /* Name: or
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> BitOut[width]
   * Fun: out = in[0] | in[1]
   * Argchecks: 
   */
  auto orFun = bitwiseA2A2AFun;
  Params orParams = widthparam;
  TypeGen orTypeGen(orParams,orFun);
  stdlib->newGeneratorDecl("or",orParams,orTypeGen);
  
  /* Name: xor
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> BitOut[width]
   * Fun: out = in[0] ^ in[1]
   * Argchecks: 
   */
  auto xorFun = bitwiseA2A2AFun;
  Params xorParams = widthparam;
  TypeGen xorTypeGen(xorParams,xorFun);
  stdlib->newGeneratorDecl("xor",xorParams,xorTypeGen);
  
  /* Name: andr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitOut[width]
   * Fun: out = &in // 1 && in
   * Argchecks: 
   */
  auto andrFun = bitwiseA2A2AFun;
  Params andrParams = widthparam;
  TypeGen andrTypeGen(andrParams,andrFun);
  stdlib->newGeneratorDecl("andr",andrParams,andrTypeGen);
  
  /* Name: orr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitOut[width]
   * Fun: out = |in  // 0 || in
   * Argchecks: 
   */
  auto orrFun = bitwiseA2A2AFun;
  Params orrParams = widthparam;
  TypeGen orrTypeGen(orrParams,orrFun);
  stdlib->newGeneratorDecl("orr",orrParams,orrTypeGen);

  /* Name: xorr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitOut[width]
   * Fun: out = ^in 
   * Argchecks: 
   */
  auto xorrFun = bitwiseA2A2AFun;
  Params xorrParams = widthparam;
  TypeGen xorrTypeGen(xorrParams,xorrFun);
  stdlib->newGeneratorDecl("xorr",xorrParams,xorrTypeGen);

  //TODO split this into multiple operators?
  /* Name: shift
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   *    shiftwidth: INT, 
   * Type: BitIn[width] -> BitOut[width]
   * Fun: out = shiftwidth > 0 ? in << shiftwidth : in >> shiftwidth 
   * Argchecks: 
   *    -width < shiftwidth < width
   */
  auto xorrFun = bitwiseA2BitFun;
  Params xorrParams = //TODO
  TypeGen xorrTypeGen(xorrParams,xorrFun);
  stdlib->newGeneratorDecl("xorr",xorrParams,xorrTypeGen);

}
