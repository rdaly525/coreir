namespace {

//template<typename To>
//typename std::enable_if<std::is_convertible<To,std::string>::value,Const*>::type
//forceCast(const Value* v) {
//  switch(v->getKind()) {
//    VK_ConstJson: return CoreIR::toString(cast<ConstJson>(v)->get());
//    default: ASSERT(0,"NYI");
//  }
//}


template<typename To>
const To& forceCast(const Value* v)  {
  ASSERT(0,"NYI");

}

}
