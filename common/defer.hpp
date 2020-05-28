#pragma once

namespace {

template <typename Fn> struct defer {
  Fn f;
  defer(Fn f) : f(f) {}
  ~defer() { f(); }
};

template <typename Fn> defer<Fn> defer_func(Fn f) { return defer<Fn>(f); }

}  // namespace

#define DEFER_1(x, y) x##y
#define DEFER_2(x, y) DEFER_1(x, y)
#define DEFER_3(x) DEFER_2(x, __COUNTER__)

// defer() is a macro for RAII semantics, ala python "with". For example, we
// could use it as follows:
//
//   void doSomething() {
//     FILE* file = fopen(...);
//     defer(fclose(file));
//     fprintf(file, "hello world\n");
//   }
//
// NOTE(rsetaluri): Though this is directly using the implementation from
// https://www.reddit.com/r/ProgrammerTIL/comments/58c6dx/til_how_to_defer_in_c/,
// there are many other similar implementations available, though nothing is in
// a common library.

#define defer(code) auto DEFER_3(_defer_) = defer_func([&]() { code; })
