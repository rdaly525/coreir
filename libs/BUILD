package(default_visibility = ["//visibility:public"])

common_deps = [ ':common',
                '//common:common',
                '//coreir-c:coreir-c_hdrs',
                '//ir/casting:casting',
                '//ir:ir_hdrs',
                '//utils:utils' ]

cc_library(
    name = 'aetherlinglib',
    hdrs = [ 'aetherlinglib.h' ],
    srcs = [ 'aetherlinglib.cpp' ],
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
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float',
    hdrs = [ 'float.h' ],
    srcs = [ 'float.cpp' ],
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float_CW',
    hdrs = [ 'float_CW.h' ],
    srcs = [ 'float_CW.cpp' ],
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'float_DW',
    hdrs = [ 'float_DW.h' ],
    srcs = [ 'float_DW.cpp' ],
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'ice40',
    hdrs = [ 'ice40.h' ],
    srcs = [ 'ice40.cpp' ],
    linkstatic = False,
    deps = common_deps)

cc_library(
    name = 'rtlil',
    hdrs = [ 'rtlil.h' ],
    srcs = [ 'rtlil.cpp' ],
    linkstatic = False,
    deps = common_deps)
