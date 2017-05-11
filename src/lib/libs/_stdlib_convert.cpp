/////////////////////////////////
// Stdlib convert primitives
//   slice,concat,cast,strip
/////////////////////////////////

inline void stdlib_convert(Context* c, Namespace* stdlib) {


  /* Name: slice
   * GenParams: 
   *    lo: UINT, The start index of the slice
   *    hi: UINT, The stop index of the slice non-inclusive
   *    arrtype: TYPE, the array type of the input.
   * Type: In(arrtype) -> Out(arrtype.elemtype)[hi-lo+1]
   * Fun: out = in[lo:hi]
   * Argchecks: 
   *    arrtype.isKind(ARRAY)
   *    start < stop <= arrtype.len
   */
  Params sliceParams({
    {"start",UINT},
    {"stop",UINT},
    {"arrtype",TYPE},
  });
  auto sliceFun = [](Context* c, Args args) { return c->Any(); } //TODO
  TypeGen sliceTypeGen(sliceParams,sliceFun);
  stdlib->newGeneratorDecl("slice",sliceParams,sliceTypeGen);

  /* Name: concat
   * GenParams: 
   *    larrtype: TYPE, the left array
   *    rarrtype: TYPE, the right array
   * Type: In(larrtype) -> In(rarrtype) -> Out(larrtype.elemtype)[larrtype.len+rarrtype.len]
   * Fun: out = concat(in[0],in[1])
   * Argchecks: 
   *    larrtype.isKind(ARRAY)
   *    rarrtype.isKind(ARRAY)
   *    larrtype.elemtype == rarrtype.elemtype
   */
  Params concatParams({
    {"larrtype",TYPE},
    {"rarrtype",TYPE}
  });
  auto concatFun = [](Context* c, Args args) { return c->Any(); } //TODO
  TypeGen concatTypeGen(concatParams,concatFun);
  stdlib->newGeneratorDecl("concat",concatParams,concatTypeGen);

  /* Name: strip
   * GenParams: 
   *    namedtype: TYPE, the type you want to strip
   * Type: namedtype -> namedtype.raw
   * Fun: out = in
   * Argchecks: 
   *    namedtype.isKind(NAMED)
   */
  Params stripParams({
    {"namedtype",TYPE}
  });
  auto stripFun = [](Context* c, Args args) { return c->Any(); } //TODO
  TypeGen stripTypeGen(stripParams,stripFun);
  stdlib->newGeneratorDecl("strip",stripParams,stripTypeGen);

  /* Name: cast
   * GenParams: 
   *    intype: TYPE, precast type
   *    outtype: TYPE, postcast type
   * Type: intype -> outype
   * Fun: out = (outtype) in
   * Argchecks: 
   *    intype.structure == outtype.structure
   */
  Params castParams({
    {"intype",TYPE},
    {"outtype",TYPE}
  });
  auto castFun = [](Context* c, Args args) { return c->Any(); } //TODO
  TypeGen castTypeGen(castParams,castFun);
  stdlib->newGeneratorDecl("cast",castParams,castTypeGen);

}

