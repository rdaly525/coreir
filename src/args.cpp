#ifndef GENARGS_CPP_
#define GENARGS_CPP_

#include "args.hpp"
#include "common.hpp"
#include "error.hpp"
#include "context.hpp"


//TODO might need to be const to make faster
//Also might be better represented virtually and overloade equals/< for each Arg
//Should do a hashing function with unordered map instead

//struct ArgHasher {
//  std::size_t operator()(const Args& ga) const {
//    
//  }
//}


namespace CoreIR {

Arg* Args::operator[](const string s) const {
  auto elem = args.find(s);
  if (elem == args.end() ) {
    Error e;
    e.message("Cannot find field \"" + s + "\" In Args");
    e.fatal();
    c->error(e);
  }
  return elem->second;
}

// TODO should just overload the == of each Arg
bool Args::ArgEq(Arg* a, Arg* b) {
  if (a->kind == b->kind) {
    switch(a->kind) {
      case ASTRING : return ((GenString*) a)->str == ((GenString*) b)->str;
      case AINT : return ((GenInt*) a)->i == ((GenInt*) b)->i;
      case ATYPE : return ((GenType*) a)->t ==  ((GenType*) b)->t;
    }
  }
  return false;
}

}//CoreIR namespace


using namespace CoreIR;

size_t std::hash<Args>::operator() (const Args& genargs) const {
  size_t hash = 0;
  for (auto it : genargs.args) {
    hash_combine(hash,it.first);
    Arg* arg = it.second;
    switch(arg->kind) {
      case ASTRING : {
        string arg_s = ((GenString*) arg)->str;
        hash_combine(hash,arg_s);
        cout << "HERE";
        break;
      }
      case AINT : {
        int arg_i = ((GenInt*) arg)->i;
        hash_combine(hash,arg_i);
        break;
      }
      case ATYPE : {
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
