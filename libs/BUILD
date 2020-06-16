package(default_visibility = ["//visibility:public"])

common_deps = [ ':common',
                '//:libcoreir.so',
                '//:libcoreir-c.so' ]
common_linkopts =  [ '-lcoreir', '-lverilogAST' ]

cc_library(
    name = 'aetherlinglib',
    hdrs = [ 'aetherlinglib.h' ],
    srcs = [ 'aetherlinglib.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps + [
        ":commonlib",
        "//libs/aetherlinglib:aetherlinglib" ])

cc_library(
    name = 'common',
    hdrs = [ 'common.h' ])

cc_library(
    name = 'commonlib',
    hdrs = [ 'commonlib.h' ],
    srcs = [ 'commonlib.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float',
    hdrs = [ 'float.h' ],
    srcs = [ 'float.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float_CW',
    hdrs = [ 'float_CW.h' ],
    srcs = [ 'float_CW.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float_DW',
    hdrs = [ 'float_DW.h' ],
    srcs = [ 'float_DW.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'ice40',
    hdrs = [ 'ice40.h' ],
    srcs = [ 'ice40.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'rtlil',
    hdrs = [ 'rtlil.h' ],
    srcs = [ 'rtlil.cpp' ],
    linkopts = common_linkopts,
    linkstatic = False,
    deps = common_deps)
