package(default_visibility = ["//visibility:public"])

cc_binary(
    name = 'coreir',
    linkstatic = True,
    srcs = [ 'coreir.cpp' ],
    deps = [ ':passlib',
             '//common:common',
             '//definitions:definitions_hdrs',
             '//ir:ir',
             '//passes/analysis:analysis',
             '//passes/transform:transform' ])

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
