//Blatently influenced by LLVM TODO how do I explicitly reference this?
//This prevents anyone from doing any dynamic casts

//Checks if val can be cast to To type
#ifndef CASTING_HPP_
#define CASTING_HPP_

namespace CoreIR {

template <typename To, typename From, typename Enabler= void>
struct isa_impl {
  static inline bool doit(const From &val) {
    return To::classof(&val);
  }
};

/// \brief Always allow upcasts, and perform no dynamic check for them.
template <typename To, typename From>
struct isa_impl<
    To, From, typename std::enable_if<std::is_base_of<To, From>::value>::type> {
  static inline bool doit(const From &) { return true; }
};

template <typename To, typename From> struct isa_impl_cl {
  static inline bool doit(const From &Val) {
    return isa_impl<To, From>::doit(Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, const From> {
  static inline bool doit(const From &Val) {
    return isa_impl<To, From>::doit(Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, From*> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, From*const> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, const From*> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

template <typename To, typename From> struct isa_impl_cl<To, const From*const> {
  static inline bool doit(const From *Val) {
    assert(Val && "isa<> used on a null pointer");
    return isa_impl<To, From>::doit(*Val);
  }
};

//TODO might not need this one
template<typename To, typename FromTy>
struct isa_impl_wrap<To, FromTy> {
  static bool doit(const FromTy &Val) {
    return isa_impl_cl<To,FromTy>::doit(Val);
  }
};


// isa<X> - Return true if the parameter to the template is an instance of the
// template type argument.  Used like this:
//
//  if (isa<Type>(myVal)) { ... }
//
template <class X, class Y>
inline bool isa(const Y &Val) {
  return isa_impl_wrap<X, const Y>::doit(Val);
}

//----------------------- cast

template<class To, class From> struct cast_retty;

// Calculate what type the 'cast' function should return, based on a requested
// type of To and a source type of From.
template<class To, class From> struct cast_retty_impl {
  typedef To& ret_type;         // Normal case, return Ty&
};
template<class To, class From> struct cast_retty_impl<To, const From> {
  typedef const To &ret_type;   // Normal case, return Ty&
};

template<class To, class From> struct cast_retty_impl<To, From*> {
  typedef To* ret_type;         // Pointer arg case, return Ty*
};

template<class To, class From> struct cast_retty_impl<To, const From*> {
  typedef const To* ret_type;   // Constant pointer arg case, return const Ty*
};

template<class To, class From> struct cast_retty_impl<To, const From*const> {
  typedef const To* ret_type;   // Constant pointer arg case, return const Ty*
};

template<class To, class From>
struct cast_retty {
  typedef typename cast_retty_impl<To,FromTy>::ret_type ret_type;
};


template<class To, class FromTy> struct cast_convert_val<To,FromTy> {
  // This _is_ a simple type, just cast it.
  static typename cast_retty<To, FromTy>::ret_type doit(const FromTy &Val) {
    typename cast_retty<To, FromTy>::ret_type Res2
     = (typename cast_retty<To, FromTy>::ret_type)const_cast<FromTy&>(Val);
    return Res2;
  }
};

// cast<X> - Return the argument parameter cast to the specified type.  This
// casting operator asserts that the type is correct, so it does not return null
// on failure.  It does not allow a null argument (use cast_or_null for that).
// It is typically used like this:
//
//  cast<Instruction>(myVal)->getParent()
//
template <class X, class Y>
inline typename cast_retty<X, const Y>::ret_type>::type
cast(const Y &Val) {
  assert(isa<X>(Val) && "cast<Ty>() argument of incompatible type!");
  return cast_convert_val<
      X, const Y>::doit(Val);
}


template <class X, class Y>
inline typename cast_retty<X, const Y>::ret_type>::type
dyn_cast(const Y &Val) {
  return isa<X>(Val) ? cast<X>(Val) : nullptr;
}

template <class X, class Y>
inline typename cast_retty<X, Y>::ret_type
dyn_cast(Y &Val) {
  return isa<X>(Val) ? cast<X>(Val) : nullptr;
}

template <class X, class Y>
inline typename cast_retty<X, Y *>::ret_type
dyn_cast(Y *Val) {
  return isa<X>(Val) ? cast<X>(Val) : nullptr;
}


}// CoreIR

#endif // CASTING_HPP_
