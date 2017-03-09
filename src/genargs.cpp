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


size_t std::hash<GenArgs>::operator() (const GenArgs& genargs) const {
  size_t hash = 0;
  for (auto it : genargs.args) {
    hash_combine(hash,it.first);
    GenArg* arg = it.second;
    switch(arg->kind) {
      case GSTRING : {
        string arg_s = ((GenString*) arg)->str;
        hash_combine(hash,arg_s);
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

//bool operator<(GenArgs l, GenArgs r) {
//  if (l.len != r.len) return l.len < r.len;
//  for (uint i=0; i< l.len; i++) {
//    if (l[i]->kind != r[i]->kind) return l[i]->kind < r[i]->kind;
//    GenArg* gl = l[i];
//    GenArg* gr = r[i];
//    switch(l[i]->kind) {
//      case GSTRING : {
//        string gls = ((GenString*) gl)->str;
//        string grs = ((GenString*) gr)->str;
//        if (gls!=grs) return gls < grs;
//        break;
//      }
//      case GINT : {
//        int gli = ((GenInt*) gl)->i;
//        int gri = ((GenInt*) gr)->i;
//        if (gli!=gri) return gli < gri;
//        break;
//      }
//      case GTYPE : {
//        Type* glt = ((GenType*) gl)->t;
//        Type* grt = ((GenType*) gr)->t;
//        if (glt!=grt) return glt < grt;
//        break;
//      }
//      default :
//        cout << "FUCK" << endl;
//        assert(false);
//    }
//
//  }
//  assert(l==r);
//  return false;
//
//}

// TODO should just overload the == of each GenArg

GenArg* GenArgs::operator[](const string s) const {
  auto elem = args.find(s);
  if (elem == args.end() ) {
    Error e;
    e.message("Cannot find field " + s + "In GenArgs");
    e.fatal();
    c->error(e);
  }
  return elem->second;
}

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

#endif //GENARGS_CPP
