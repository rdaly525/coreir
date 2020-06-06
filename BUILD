package(default_visibility = ["//visibility:public"])

load('//:defs.bzl', 'install_lib')
load('//:defs.bzl', 'install_bin')
load('//:defs.bzl', 'install_hdrs')
load('//:defs.bzl', 'install_all_hdrs')
load('//:defs.bzl', 'install_set')

install_set(
    name = "install",
    deps = [ ":install_aetherlinglib",
             ":install_commonlib",
             ":install_float",
             ":install_float_CW",
             ":install_float_DW",
             ":install_ice40",
             ":install_rtlil",
             ":install_coreir",
             ":install_ir_hdrs",
             ":install_common_hdrs",
             ":install_utils_hdrs",
             ":install_passes_hdrs",
             ":install_passes_analysis_hdrs",
             ":install_passes_transform_hdrs" ])

install_lib(
    name = "install_aetherlinglib",
    lib = "//libs:aetherlinglib",
    rename = "libcoreir-aetherlinglib.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_commonlib",
    lib = "//libs:commonlib",
    rename = "libcoreir-commonlib.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float",
    lib = "//libs:float",
    rename = "libcoreir-float.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float_CW",
    lib = "//libs:float_CW",
    rename = "libcoreir-float_CW.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_float_DW",
    lib = "//libs:float_DW",
    rename = "libcoreir-float_DW.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_ice40",
    lib = "//libs:ice40",
    rename = "libcoreir-ice40.dylib",
    subdirectory = "lib",
    default_directory = "/usr/local")

install_lib(
    name = "install_rtlil",
    lib = "//libs:rtlil",
    rename = "libcoreir-rtlil.dylib",
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
