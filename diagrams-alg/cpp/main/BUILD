
cc_binary(
  name = "diagrams-equalizer",
  srcs = [ "main.cpp",
           "diagram.cpp", "diagram.hpp",
           "diagram_builder.cpp", "diagram_builder.hpp",
           "eq_type.cpp", "eq_type.hpp",
           "sparse_matrix_iterator.hpp" ],
  deps = [ "@eigen//:inc",
           "@com_google_absl//absl/container:flat_hash_map",
           "@com_google_absl//absl/container:inlined_vector",
           "@com_google_absl//absl/types:span",
         ]
)
