package(default_visibility = ["//visibility:public"])

load("@rules_foreign_cc//tools/build_defs:cmake.bzl", "cmake_external")
load('//:defs.bzl', 'platform_specific_shared_libraries')

cmake_external(
    name = "verilogAST",
    lib_source = "@verilogAST//:all",
    shared_libraries = platform_specific_shared_libraries([ "libverilogAST" ]),
    static_libraries = [])
