package(default_visibility = ["//visibility:public"])

load("@rules_foreign_cc//tools/build_defs:cmake.bzl", "cmake_external")

cmake_external(
    name = "verilogAST",
    lib_source = "@verilogAST//:all",
    shared_libraries = [ "libverilogAST.dylib" ],
    static_libraries = []
)
