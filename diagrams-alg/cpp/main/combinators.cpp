#include "combinators.hpp"

Diagram node(const CoqObject& o, absl::string_view name) {
    Diagram ret;
    if(!name.empty()) {
        ret.nodes_ids.insert_or_assign(name, ret.nodes.size());
    }
    ret.nodes.push_back(Node{static_cast<std::string>(name), o});
    return ret;
}

Diagram applyF(absl::string_view functor_name, const Diagram& d) {
    // TODO
}

Diagram makeIso(const Diagram& d, absl::string_view name) {
    // TODO
}

Diagram pushout(const Diagram& d1, const Diagram& d2) {
    // TODO
}
