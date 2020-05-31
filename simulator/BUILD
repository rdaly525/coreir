package(default_visibility = ["//visibility:public"])

cc_library(
    name = 'simulator',
    srcs = [ 'codegen.cpp',
             'dag_optimiziation.cpp',
             'interpret.cpp',
             'layout.cpp',
             'low_rep.cpp',
             'multithreading.cpp',
             'output.cpp',
             'print_c.cpp',
             'sim.cpp',
             'subcircuit.cpp' ],
    deps = [ ':simulator_hdrs',
             '//common:common',
             '//ir/casting:casting',
             '//ir:ir_hdrs',
             '//passes/transform:transform',
             '//utils:utils' ])

cc_library(
    name = 'simulator_hdrs',
    hdrs = [ 'bsim_lib.hpp',
             'codegen.h',
             'coreirsim.h',
             'dag_optimization.h',
             'interpreter.h',
             'layout.h',
             'low_rep.h',
             'multithreading.h',
             'output.h',
             'print_c.h',
             'simulator.h',
             'subcircuit.h' ])
