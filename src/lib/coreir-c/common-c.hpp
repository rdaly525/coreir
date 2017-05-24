//Common functions for c-api implementations
template <class T1, class T2>
T1 rcast(T2 in) {
  return reinterpret_cast<T1>(in);
}

