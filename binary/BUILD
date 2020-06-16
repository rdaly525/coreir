package(default_visibility = ["//visibility:public"])

cc_binary(
    name = 'coreir',
    linkopts = [ '-lcoreir' ],
    srcs = [ 'coreir.cpp' ],
    deps = [ ':passlib',
             '//:libcoreir.so',
             '//:libcoreir-c.so',
             '//external/verilogAST:verilogAST' ])

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
