
cc_library(
    name = "diagrams-equalizer-lib",
    srcs = [ "diagram.cpp",
             "diagram_builder.cpp",
             "eq_type.cpp",
             "commutation.cpp",
             "combinators.cpp",
            ],
    hdrs = [ "diagram.hpp",
             "diagram_builder.hpp",
             "eq_type.hpp",
             "commutation.hpp",
             "combinators.hpp",
            ],
    deps = [ "@com_google_absl//absl/container:flat_hash_map",
             "@com_google_absl//absl/container:inlined_vector",
             "@com_google_absl//absl/strings",
             "@com_google_absl//absl/types:span",
            ],
)

cc_binary(
    name = "diagrams-equalizer",
    srcs = [ "main.cpp" ],
    deps = [ ":diagrams-equalizer-lib" ],
)

cc_test(
    name = "commutation_test",
    size = "small",
    srcs = [ "commutation_tests.cpp" ],
    deps = [ "@com_google_googletest//:gtest_main",
             ":diagrams-equalizer-lib",
            ],
)
