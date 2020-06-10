package(default_visibility = ["//visibility:public"])

cc_binary(
    name = 'coreir',
    linkstatic = True,
    srcs = [ 'coreir.cpp' ],
    deps = [ ':passlib',
             '//:coreir' ])

cc_binary(
    name = 'interpreter',
    srcs = [ 'interpreter.cpp' ],
    deps = [ ':passlib',
             '//:coreir',
             '//libs:commonlib' ])

cc_binary(
    name = 'simulator',
    srcs = [ 'simulator.cpp' ],
    deps = [ ':passlib',
             '//:coreir',
             '//libs:commonlib' ])

cc_library(
    name = 'passlib',
    hdrs = [ 'passlib.h' ])
