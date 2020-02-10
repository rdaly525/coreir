cc_binary(
    name = 'my_test',
    srcs = [ 'test.cpp' ],
    deps = [ ':coreir_context' ])

cc_library(
    name = 'array_type',
    hdrs = [ 'array_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'array_type_cache',
    hdrs = [ 'array_type_cache.hpp' ],
    srcs = [ 'array_type_cache.cpp' ],
    deps = [ ':array_type' ])

cc_library(
    name = 'bit_in_out_type',
    hdrs = [ 'bit_in_out_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'bit_in_type',
    hdrs = [ 'bit_in_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'bit_type',
    hdrs = [ 'bit_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'contextual',
    hdrs = [ 'contextual.hpp' ],
    deps = [ 'coreir_context_interface' ])

cc_library(
    name = 'coreir_context',
    hdrs = [ 'coreir_context.hpp' ],
    deps = [ ':array_type',
             ':bit_in_out_type',
             ':bit_in_type',
             ':bit_type',
             ':coreir_context_interface',
             ':named_type',
             ':record_type',
             ':type_cache' ])

cc_library(
    name = 'coreir_context_interface',
    hdrs = [ 'coreir_context_interface.hpp' ])

cc_library(
    name = 'named_type',
    hdrs = [ 'named_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'record_type',
    hdrs = [ 'record_type.hpp' ],
    deps = [ ':type' ])

cc_library(
    name = 'type',
    hdrs = [ 'type.hpp' ],
    deps = [ ':contextual' ])

cc_library(
    name = 'type_cache',
    hdrs = [ 'type_cache.hpp' ],
    deps = [ 'array_type_cache' ])
