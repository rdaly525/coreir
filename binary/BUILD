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

cc_binary(
    name = 'interpreter',
    srcs = [ 'interpreter.cpp' ],
    deps = [ ':passlib',
             '//ir:ir',
             '//libs:libs',
             '//passes/analysis:analysis',
             '//simulator:simulator' ])

cc_binary(
    name = 'simulator',
    srcs = [ 'simulator.cpp' ],
    deps = [ '//ir:ir',
             '//libs:libs',
             '//passes/analysis:analysis',
             '//simulator:simulator' ])

cc_library(
    name = 'passlib',
    hdrs = [ 'passlib.h' ])
