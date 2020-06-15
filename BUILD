package(default_visibility = ["//visibility:public"])

load('//:defs.bzl', 'install_lib')
load('//:defs.bzl', 'install_bin')
load('//:defs.bzl', 'install_all_hdrs')
load('//:defs.bzl', 'install_set')
load('//:defs.bzl', 'platform_specific_shared_library')

cc_library(
    name = "coreir",
    linkopts = [ '-ldl' ],
    srcs = [ '//common:common_srcs',
             '//ir:ir_srcs',
             '//passes/analysis:analysis_srcs',
             '//passes/transform:transform_srcs',
             '//simulator:simulator_srcs' ],
    hdrs = [ '//common:common_hdrs',
             '//definitions:definitions_hdrs',
             '//ir:ir_hdrs',
             '//ir/casting:casting_hdrs',
             '//ir/headers:headers_hdrs',
             '//passes:passes_hdrs',
             '//passes/analysis:analysis_hdrs',
             '//passes/transform:transform_hdrs',
             '//simulator:simulator_hdrs',
             '//utils:utils_hdrs' ],
    deps = [ '//external/verilogAST:verilogAST' ])

cc_library(
    name = "coreir-c",
    srcs = [ '//coreir-c:coreir-c_srcs' ],
    hdrs = [ '//coreir-c:coreir-c_hdrs' ],
    deps = [ ':coreir',
             '//external/verilogAST:verilogAST' ])

install_set(
    name = "install",
    deps = [ ":install_aetherlinglib",
             ":install_commonlib",
             ":install_float",
             ":install_float_CW",
             ":install_float_DW",
             ":install_ice40",
             ":install_libcoreir",
             ":install_libcoreir-c",
             ":install_rtlil",
             ":install_coreir",
             ":install_ir_hdrs",
             ":install_common_hdrs",
             ":install_utils_hdrs",
             ":install_passes_hdrs",
             ":install_passes_analysis_hdrs",
             ":install_passes_transform_hdrs" ])

install_lib(
    name = "install_libcoreir",
    lib = ":coreir",
    rename = platform_specific_shared_library("libcoreir"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_libcoreir-c",
    lib = ":coreir-c",
    rename = platform_specific_shared_library("libcoreir-c"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_aetherlinglib",
    lib = "//libs:aetherlinglib",
    rename = platform_specific_shared_library("libcoreir-aetherlinglib"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_commonlib",
    lib = "//libs:commonlib",
    rename = platform_specific_shared_library("libcoreir-commonlib"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float",
    lib = "//libs:float",
    rename = platform_specific_shared_library("libcoreir-float"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float_CW",
    lib = "//libs:float_CW",
    rename = platform_specific_shared_library("libcoreir-float_CW"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float_DW",
    lib = "//libs:float_DW",
    rename = platform_specific_shared_library("libcoreir-float_DW"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_ice40",
    lib = "//libs:ice40",
    rename = platform_specific_shared_library("libcoreir-ice40"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_rtlil",
    lib = "//libs:rtlil",
    rename = platform_specific_shared_library("libcoreir-rtlil"),
    subdirectory = "lib",
    default_directory = "/usr/local")

install_bin(
    name = "install_coreir",
    bin = "//binary:coreir",
    subdirectory = "bin",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "ir",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "common",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "utils",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "passes",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "passes/analysis",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")

install_all_hdrs(
    path = "passes/transform",
    subdirectory = "include/coreir",
    default_directory = "/usr/local")
