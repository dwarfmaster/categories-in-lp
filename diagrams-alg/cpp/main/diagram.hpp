#ifndef DEF_DIAGRAM
#define DEF_DIAGRAM

#include "absl/container/inlined_vector.h"
#include "absl/container/flat_hash_map.h"
#include <iostream>
#include <vector>
#include "eq_type.hpp"

struct Arrow {
    unsigned src, dst;
    std::string name;
    bool isMono, isEpi, isIso;
    // If isIso, which arrow is its inverse in the diagram
    unsigned inverse;
    Arrow(unsigned s, unsigned d, const std::string& n)
        : src(s), dst(d), name(n), isMono(false), isEpi(false), isIso(false), inverse(0) {}
};

struct Diagram;

struct Path {
    using Vector = absl::InlinedVector<unsigned,58>;
    Vector arrows;
    const Diagram* diag;
    unsigned src;

    inline bool operator==(const Path& p) const {
        return src == p.src && arrows == p.arrows;
    }

    template <typename H>
    friend H AbslHashValue(H h, const Path& p) {
        return H::combine(std::move(h), p.src, p.arrows);
    }

    // Returns true if already normal
    bool normalize();
    // Is identity
    inline bool isId() const { return arrows.empty(); }
    // Extend to the right while preserving normalisation
    void precompose(unsigned arrow);
    void precompose(const Path& p);
    // Extend to the left while preserving normalisation
    void postcompose(unsigned arrow);
    void postcompose(const Path& p);
};
static_assert(sizeof(Path) == 64 * sizeof(unsigned), "Path must be of size 64");

struct Diagram {
    unsigned nb_nodes;
    std::vector<Arrow> edges;
    std::vector<std::pair<Path,Path>> faces;

    inline unsigned src(const Path& p) {
        return p.src;
    }
    inline unsigned dst(const Path& p) {
        if(p.arrows.empty()) return p.src;
        else return edges[p.arrows.back()].dst;
    }
};

// Path utilities
unsigned path_dst(const Path& p);
Path subpath(const Path& p, unsigned start, unsigned end);
Path path_prefix(const Path& p, unsigned end);
Path path_suffix(const Path& p, unsigned start);
Path path_concat(const Path& p1, const Path& p2);
Path mkPath(const Diagram& d, unsigned arrow);
Path mkPath2(const Diagram& d, unsigned a1, unsigned a2);
Path consPath(const Diagram& d, unsigned arrow, const Path& p);
std::ostream& operator<<(std::ostream& os, const Path p);

// Diagrams utilities
void addEq(Diagram& d, const Path& p1, const Path& p2);
void addEq(Diagram& d, Path&& p1, Path&& p2);

#endif
