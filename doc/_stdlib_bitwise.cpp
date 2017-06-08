/////////////////////////////////
// Stdlib Bitwise primitives
//   not,and,or,xor,andr,orr,xorr
/////////////////////////////////

using namespace CoreIR;

void stdlib_bitwise(Context* c, Namespace* stdlib) {
  
  //Template
  /* Name: 
   * GenParams: 
   *    <Argname>: <Argtype>, <description>
   * Type: 
   * Fun: 
   * Argchecks: 
   */
  
  Params widthparams({{"width",AINT}});

  /* Name: not
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = ~in
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("not",stdlib->getTypeGen("unary"),widthparams);
  
  /* Name: and
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> Bit[width]
   * Fun: out = in[0] & in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("and",stdlib->getTypeGen("binary"),widthparams);
  
  /* Name: or
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> Bit[width]
   * Fun: out = in[0] | in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("or",stdlib->getTypeGen("binary"),widthparams);
  
  /* Name: xor
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> BitIn[width] -> Bit[width]
   * Fun: out = in[0] ^ in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("xor",stdlib->getTypeGen("binary"),widthparams);
  
  /* Name: andr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = &in // 1 && in
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("andr",stdlib->getTypeGen("unaryReduce"),widthparams);
  
  /* Name: orr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = |in  // 0 || in
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("orr",stdlib->getTypeGen("unaryReduce"),widthparams);

  /* Name: xorr
   * GenParams: 
   *    width: UINT, bitwidth
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = ^in 
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("xorr",stdlib->getTypeGen("unaryReduce"),widthparams);

  /* Name: shl
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   *    shiftbits: INT, 
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = in << shiftbits
   * Argchecks: 
   */
  Params shiftparamss({{"width",AINT},{"shiftbits",AINT}});
  stdlib->newGeneratorDecl("shl",stdlib->getTypeGen("unary"),shiftparamss);
  
  /* Name: lshr
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   *    shiftbits: INT, 
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = in >>> shiftbits
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("lshr",stdlib->getTypeGen("unary"),shiftparamss);
  
  /* Name: ashr
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   *    shiftbits: INT, 
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = in >> shiftbits
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("ashr",stdlib->getTypeGen("unary"),shiftparamss);

  /* Name: dshl
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   * Type: BitIn[width][2] -> Bit[width]
   * Fun: out = in[0] << in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("dshl",stdlib->getTypeGen("binary"),widthparams);
  
  /* Name: dlshr
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = in[0] >>> in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("dlshr",stdlib->getTypeGen("binary"),widthparams);
  
  /* Name: ashr
   * GenParams: 
   *    width: UINT, bitwidth of input and output
   * Type: BitIn[width] -> Bit[width]
   * Fun: out = in[0] >> in[1]
   * Argchecks: 
   */
  stdlib->newGeneratorDecl("dashr",stdlib->getTypeGen("binary"),widthparams);


}
