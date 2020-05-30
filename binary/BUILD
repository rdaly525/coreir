package(default_visibility = ["//visibility:public"])

cc_binary(
    name = 'coreir',
    srcs = [ 'coreir.cpp' ],
    deps = [ ':passlib',
             '//common:common',
             '//definitions:definitions',
             '//ir:ir',
             '//ir/casting:casting',
             '//passes/analysis:analysis',
             '//passes/transform:transform',
             '//utils:utils' ])

cc_library(
    name = 'passlib',
    hdrs = [ 'passlib.h' ])
