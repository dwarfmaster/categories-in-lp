#include <iostream>
#include <vector>
#include <string>
#include <cassert>
#include <span>
#include <chrono>

#include "absl/types/span.h"

#include "eq_type.hpp"
#include "diagram.hpp"
#include "commutation.hpp"
#include "diagram_builder.hpp"

// TODO understand how to make heterogeneous lookup work
class PathView {
    unsigned src_;
    absl::Span<const unsigned> arrows_view_;

    public:
        PathView(const Path& p, unsigned start, unsigned end) {
            assert(end <= p.arrows.size());
            assert(start < end);
            if(start == 0) src_ = p.src;
            else           src_ = p.diag->edges[p.arrows[start]].src;
            arrows_view_ = absl::MakeSpan(p.arrows).subspan(start, end - start);
        }
        static PathView makePrefix(const Path& p, unsigned end) {
            assert(0 < end);
            return PathView(p, 0, end);
        }
        static PathView makeSuffix(const Path& p, unsigned start) {
            assert(start < p.arrows.size());
            return PathView(p, start, p.arrows.size());
        }

        unsigned src() const {
            return src_;
        }

        bool operator==(const PathView& p) {
            return src_ == p.src_ && arrows_view_ == p.arrows_view_;
        }
        template <typename H>
        friend H AbslHashValue(H h, const PathView& p) {
            return H::combine(std::move(h), p.src_, p.arrows_view_);
        }
};

void queryGraph(const Diagram& d) {
    CommutationCache cache = buildCmCache("interactive", std::cout, d, 2);
    unsigned p1, p2;
    while(true) {
        std::cout << "All paths[" << cache.all_paths.size() << "]:\n";
        for(unsigned p = 0; p < cache.all_paths.size(); ++p) {
            std::cout << "[" << p << "] " << cache.all_paths[p] << "\n";
        }

        std::cout << std::endl;
        std::cout << "Enter first path: ";
        std::cin >> p1;
        if(p1 >= cache.all_paths.size()) {
            std::cout << "Terminating" << std::endl;
            return;
        }
        std::cout << "Enter second path: ";
        std::cin >> p2;
        if(p2 >= cache.all_paths.size()) {
            std::cout << "Terminating" << std::endl;
            return;
        }

        std::cout << ">>>>>> " << cache.all_paths[p1] << " = " << cache.all_paths[p2]
            << " ? " << cache.comm_mat.coeff(p1, p2) << " <<<<<<\n\n";
    }
}

int main(int, char**) {
    DiagramBuilder d;
    std::cout << "Addings nodes" << std::endl;
    d.addNode("a");
    d.addNode("b");
    d.addNode("c");
    d.addNode("d");
    d.addNode("p");
    std::cout << "Adding arrows" << std::endl;
    d.addArrow("f", "b", "d");
    d.addArrow("g", "c", "d");
    d.addArrow("h", "a", "d");
    d.addArrow("pi1", "a", "b");
    d.addArrow("pi2", "a", "c");
    d.addArrow("fpi1", "p", "b");
    d.addArrow("fpi2", "p", "c");
    d.addArrow("uniq", "p", "a");
    std::cout << "Addings faces" << std::endl;
    d.addFace(d.mkPath("h"), d.mkPath<std::string>("pi1", "f"));
    d.addFace(d.mkPath("h"), d.mkPath<std::string>("pi2", "g"));
    d.addFace(d.mkPath("fpi1"), d.mkPath<std::string>("uniq", "pi1"));
    d.addFace(d.mkPath("fpi2"), d.mkPath<std::string>("uniq", "pi2"));
    std::cout << "Building" << std::endl;
    Diagram diag = d.build();
    std::cout << "Querying" << std::endl;
    queryGraph(diag);

    return 0;
}
