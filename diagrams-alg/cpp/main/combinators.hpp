#ifndef DEF_COMBINATORS
#define DEF_COMBINATORS

#include <vector>
#include "absl/strings/string_view.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/inlined_vector.h"

// Stand-in for the coq value
struct CoqObject {
    std::string name;
};
inline CoqObject coq(absl::string_view name) {
    return CoqObject{ static_cast<std::string>(name) };
}

struct Node {
    std::string name;
    CoqObject object;
};

struct Arrow {
    std::string name;
    CoqObject object;
    unsigned src;
    unsigned dst;
};

struct Path {
    using Vector = absl::InlinedVector<unsigned,27>;
    Vector arrows;
    unsigned src;
};
static_assert(sizeof(Path) == 32 * sizeof(unsigned), "Path must be of size 32");

struct Diagram {
    std::vector<Node> nodes;
    absl::flat_hash_map<absl::string_view,unsigned> nodes_ids;
    std::vector<Arrow> edges;
    std::vector<std::pair<Path,Path>> faces;
};

//  ____            _
// | __ )  __ _ ___(_) ___
// |  _ \ / _` / __| |/ __|
// | |_) | (_| \__ \ | (__
// |____/ \__,_|___/_|\___|
// Basic combinators, implemented directly by low-level diagram manipulation
// These form the "interface" to buil diagrams from

// Create a diagram with only one node
Diagram node(const CoqObject& object, absl::string_view name = "");
// Take the union of two graphs, and apply F to all pairs of nodes, one is src,
// one in dst to potentially connect them. F must be a lambda that takes a src
// and a dst node and returns an optional tuple <name,object,isEpi,isMono> of
// type std::tuple<std::string,CoqObject,bool,bool>
template <typename F>
Diagram connect(const Diagram& src, const Diagram& dst, F name);
// Potentially fill all faces with borders of length at most *length* in the
// diagrams. F must takes two paths and return an optional boolean between them
template <typename F>
Diagram fill(const Diagram& d, F name, unsigned length);
// Take the image by a functor
Diagram applyF(absl::string_view functor_name, const Diagram& d);
// Make an arrow in the diagram an isomorphism
Diagram makeIso(const Diagram& d, absl::string_view name);
// Take the pushout of two diagrams, without duplicating the common objects.
Diagram pushout(const Diagram& d1, const Diagram& d2);

//  _   _ _       _           _                   _
// | | | (_) __ _| |__       | |    _____   _____| |
// | |_| | |/ _` | '_ \ _____| |   / _ \ \ / / _ \ |
// |  _  | | (_| | | | |_____| |__|  __/\ V /  __/ |
// |_| |_|_|\__, |_| |_|     |_____\___| \_/ \___|_|
//          |___/
// High-level combinators, implemented only in terms of low-level combinators



//  ___                 _                           _        _   _
// |_ _|_ __ ___  _ __ | | ___ _ __ ___   ___ _ __ | |_ __ _| |_(_) ___  _ __
//  | || '_ ` _ \| '_ \| |/ _ \ '_ ` _ \ / _ \ '_ \| __/ _` | __| |/ _ \| '_ `
//  | || | | | | | |_) | |  __/ | | | | |  __/ | | | || (_| | |_| | (_) | | | |
// |___|_| |_| |_| .__/|_|\___|_| |_| |_|\___|_| |_|\__\__,_|\__|_|\___/|_| |_|
//               |_|
// Implementation of template methods

template <typename F>
Diagram connect(const Diagram& src, const Diagram& dst, F name) {
    // TODO
}

template <typename F>
Diagram fill(const Diagram& d, F name) {
    // TODO
}

#endif // DEF_COMBINATORS
