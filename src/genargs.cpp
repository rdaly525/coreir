#ifndef GENARGS_CPP_
#define GENARGS_CPP_

#include "genargs.hpp"
#include "common.hpp"

//TODO might need to be const to make faster
//Also might be better represented virtually and overloade equals/< for each GenArg
//Should do a hashing function with unordered map instead

//struct GenArgHasher {
//  std::size_t operator()(const GenArgs& ga) const {
//    
//  }
//}


namespace CoreIR {

GenArg* GenArgs::operator[](const string s) const {
  auto elem = args.find(s);
  if (elem == args.end() ) {
    Error e;
    e.message("Cannot find field \"" + s + "\" In GenArgs");
    e.fatal();
    c->error(e);
  }
  return elem->second;
}

// TODO should just overload the == of each GenArg
bool GenArgs::GenArgEq(GenArg* a, GenArg* b) {
  if (a->kind == b->kind) {
    switch(a->kind) {
      case GSTRING : return ((GenString*) a)->str == ((GenString*) b)->str;
      case GINT : return ((GenInt*) a)->i == ((GenInt*) b)->i;
      case GTYPE : return ((GenType*) a)->t ==  ((GenType*) b)->t;
    }
  }
  return false;
}

}//CoreIR namespace


using namespace CoreIR;

size_t std::hash<GenArgs>::operator() (const GenArgs& genargs) const {
  size_t hash = 0;
  for (auto it : genargs.args) {
    hash_combine(hash,it.first);
    GenArg* arg = it.second;
    switch(arg->kind) {
      case GSTRING : {
        string arg_s = ((GenString*) arg)->str;
        hash_combine(hash,arg_s);
        cout << "HERE";
        break;
      }
      case GINT : {
        int arg_i = ((GenInt*) arg)->i;
        hash_combine(hash,arg_i);
        break;
      }
      case GTYPE : {
        Type* arg_t = ((GenType*) arg)->t;
        hash_combine(hash,arg_t);
        break;
      }
      default : 
        assert(false);
    }
  }
  return hash;
}

#endif //GENARGS_CPP
