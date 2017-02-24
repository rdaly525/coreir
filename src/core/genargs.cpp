#ifndef GENARGS_CPP_
#define GENARGS_CPP_

#include "genargs.hpp"
#include "enums.hpp"

//TODO might need to be const to make faster
//Also might be better represented virtually and overloade equals/< for each GenArg
bool operator<(GenArgs l, GenArgs r) {
  if (l.len != r.len) return l.len < r.len;
  for (uint i=0; i< l.len; i++) {
    if (l[i]->kind != r[i]->kind) return l[i]->kind < r[i]->kind;
    GenArg* gl = l[i];
    GenArg* gr = r[i];
    switch(l[i]->kind) {
      case GSTRING : {
        string gls = ((GenString*) gl)->str;
        string grs = ((GenString*) gr)->str;
        if (gls!=grs) return gls < grs;
        break;
      }
      case GINT : {
        int gli = ((GenInt*) gl)->i;
        int gri = ((GenInt*) gr)->i;
        if (gli!=gri) return gli < gri;
        break;
      }
      case GTYPE : {
        Type* glt = ((GenType*) gl)->t;
        Type* grt = ((GenType*) gr)->t;
        if (glt!=grt) return glt < grt;
        break;
      }
      default :
        cout << "FUCK" << endl;
        assert(false);
    }

  }
  cout << "THE EXACT SAME\n";
  assert(l==r);
  return false;

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
