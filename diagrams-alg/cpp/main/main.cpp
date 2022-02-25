#include <iostream>
#include <vector>
#include <string>
#include <cassert>
#include <span>
#include <chrono>
#include <Eigen/Sparse>

#include "absl/container/flat_hash_map.h"
#include "absl/container/inlined_vector.h"
#include "absl/types/span.h"

#include "eq_type.hpp"
#include "sparse_matrix_iterator.hpp"

struct Arrow {
    unsigned src, dst;
    std::string name;
    Arrow(unsigned s, unsigned d, const std::string& n) : src(s), dst(d), name(n) {}
};

struct Diagram;

struct Path {
    using Vector = absl::InlinedVector<unsigned,62>;
    Vector arrows;
    const Diagram* diag;
    unsigned src;

    bool operator==(const Path& p) const {
        return src == p.src && arrows == p.arrows;
    }

    template <typename H>
    friend H AbslHashValue(H h, const Path& p) {
        return H::combine(std::move(h), p.src, p.arrows);
    }
};

struct Diagram {
    unsigned nb_nodes;
    std::vector<Arrow> edges;
    std::vector<std::pair<Path,Path>> faces;

    unsigned src(const Path& p) {
        return p.src;
    }
    unsigned dst(const Path& p) {
        if(p.arrows.empty()) return p.src;
        else return edges[p.arrows.back()].dst;
    }
};

unsigned path_dst(const Path& p) {
    if(p.arrows.empty()) return p.src;
    else return p.diag->edges[p.arrows.back()].dst;
}

Path subpath(const Path& p, unsigned start, unsigned end) {
    assert(start < end);
    assert(end <= p.arrows.size());
    Path ret;
    ret.diag = p.diag;
    if(start == 0) ret.src = p.src;
    else           ret.src = p.diag->edges[p.arrows[start]].src;
    ret.arrows = Path::Vector(p.arrows.begin() + start, p.arrows.begin() + end);
    return ret;
}

Path path_prefix(const Path& p, unsigned end) {
    return subpath(p, 0, end);
}

Path path_suffix(const Path& p, unsigned start) {
    return subpath(p, start, p.arrows.size());
}

Path path_concat(const Path& p1, const Path& p2) {
    assert(p1.diag == p2.diag);
    Path result;
    result.diag = p1.diag;
    result.src = p1.src;
    result.arrows.resize(p1.arrows.size() + p2.arrows.size());
    auto it = std::copy(p1.arrows.begin(), p1.arrows.end(), result.arrows.begin());
    std::copy(p2.arrows.begin(), p2.arrows.end(), it);
    return result;
}

std::ostream& operator<<(std::ostream& os, const Path p) {
    if(p.arrows.empty()) {
        os << "id_" << p.src << "\n";
        return os;
    }
    for(auto it = p.arrows.rbegin(), end = p.arrows.rend(); it != end; ++it) {
        os << p.diag->edges[*it].name;
        if(it + 1 != end) std::cout << " o ";
    }
    return os;
}

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

void addEq(Diagram& d, const Path& p1, const Path& p2) {
    assert(p1.diag == std::addressof(d));
    assert(p2.diag == std::addressof(d));
    assert(path_dst(p1) == p2.src);
    d.faces.push_back(std::make_pair(p1, p2));
}
void addEq(Diagram& d, Path&& p1, Path&& p2) {
    d.faces.push_back(std::make_pair(p1, p2));
}

Path mkPath(const Diagram& d, unsigned arrow) {
    return { { arrow }, std::addressof(d), d.edges[arrow].src };
}
Path mkPath2(const Diagram& d, unsigned a1, unsigned a2) {
    assert(d.edges[a1].dst == d.edges[a2].src);
    return { { a1, a2 }, std::addressof(d), d.edges[a1].src };
}
Path consPath(const Diagram& d, unsigned arrow, const Path& p) {
    assert(d.edges[arrow].dst == p.src);
    Path::Vector steps;
    steps.resize(p.arrows.size() + 1);
    steps[0] = arrow;
    std::copy(p.arrows.begin(), p.arrows.end(), steps.begin() + 1);
    return { steps, std::addressof(d), d.edges[arrow].src };
}

std::vector<Path> enumeratePathsOfSize(const Diagram& d, size_t maxSize) {
    assert(maxSize > 0);
    std::vector<Path> result;
    std::vector<std::vector<Path>> connections;
    connections.resize(d.nb_nodes * d.nb_nodes);

    // connections initialization
    for(size_t a = 0; a < d.edges.size(); ++a) {
        connections[d.edges[a].src * d.nb_nodes + d.edges[a].dst].push_back(mkPath(d, a));
    }

    // Grow paths
    std::vector<unsigned> oldSizes(connections.size(), 0);
    for(size_t size = 1; size < maxSize; ++size) {
        for(size_t cn = 0; cn < connections.size(); ++cn) oldSizes[cn] = connections[cn].size();
        for(size_t a = 0; a < d.edges.size(); ++a) {
            for(size_t dest = 0; dest < d.nb_nodes; ++dest) {
                unsigned outId = d.edges[a].dst * d.nb_nodes + dest;
                for(size_t old = 0; old < oldSizes[outId]; ++old) {
                    Path npath = consPath(d, a, connections[outId][old]);
                    connections[d.edges[a].src * d.nb_nodes + dest].push_back(npath);
                }
            }
        }
    }

    // Concatenate all results
    size_t finalSize = 0;
    for(size_t i = 0; i < connections.size(); ++i) finalSize += connections[i].size();
    result.resize(finalSize);
    for(size_t i = 0, pth = 0; i < connections.size(); ++i) {
        for(size_t p = 0; p < connections[i].size(); ++p, ++pth) {
            result[pth] = std::move(connections[i][p]);
        }
    }
    return result;
}

struct CommutationCache {
    using EqMat = Eigen::SparseMatrix<EqType>;
    Diagram d;
    std::vector<Path> all_paths;
    absl::flat_hash_map<Path,unsigned> path_ids;
    EqMat comm_mat;
};

bool eq_path(const Path& p1, const Path& p2) {
    return p1.src == p2.src
        && p1.arrows.size() == p2.arrows.size()
        && std::equal(p1.arrows.begin(), p1.arrows.end(), p2.arrows.begin());
}

// cost is a number that constrain the solver, since the problem in undecidable
// in general
CommutationCache mkCmCache(const Diagram& d, unsigned cost) {
    CommutationCache result;
    result.d = d;
    result.all_paths = enumeratePathsOfSize(d, cost+1);
    unsigned nb_paths = result.all_paths.size();

    // Later completion could be optimised using a hash-map supporting a rolling
    // hash
    result.path_ids.reserve(nb_paths);
    for(unsigned p = 0; p < nb_paths; ++p) result.path_ids.insert({ result.all_paths[p], p });

    // Since adding a new non-zero entry is costly, with first create a list of
    // triplets and initialize all the matrix at once
    using T = Eigen::Triplet<EqType>;
    std::vector<T> entries;
    entries.reserve(nb_paths + d.faces.size() * 2 + nb_paths * 2); // The last one is heuristic
    // Fill the diagonal
    for(unsigned p = 0; p < nb_paths; ++p) entries.push_back(T(p,p,EqType(true)));
    // Fill pre-existing faces
    for(unsigned f = 0; f < d.faces.size(); ++f) {
        unsigned p1 = result.path_ids[d.faces[f].first];
        unsigned p2 = result.path_ids[d.faces[f].second];
        entries.push_back(T(p1,p2,EqType(true)));
        entries.push_back(T(p2,p1,EqType(true)));
    }
    result.comm_mat.resize(nb_paths, nb_paths);
    result.comm_mat.setFromTriplets(entries.begin(), entries.end());

    return result;
}

// Combutes base * x^pow into base
template <typename T>
void fastpow_into(T& base, T x, unsigned pow) {
    while(pow > 0) {
        if(pow%2 == 0) {
            pow /= 2;
            x = x * x;
        } else {
            base = base * x;
            pow -= 1;
        }
    }
}

// TODO doesn't work
void contextCloseCache(CommutationCache& cache) {
    CommutationCache::EqMat result = cache.comm_mat;

    for(unsigned p = 0; p < cache.all_paths.size(); ++p) {
        const Path& path = cache.all_paths[p];
        for(size_t split = 1; split < path.arrows.size(); ++split) {
            unsigned prefix = cache.path_ids[path_prefix(path, split)];
            unsigned suffix = cache.path_ids[path_suffix(path, split)];

            for(SparseMatrixInnerIterator<EqType> prefix_it(cache.comm_mat, prefix),
                  prefix_end = SparseMatrixInnerIterator<EqType>::makeEnd(cache.comm_mat, prefix);
              prefix_it != prefix_end; ++prefix_it) {
                if(*prefix_it != EqType(true)) continue;
                for(SparseMatrixInnerIterator<EqType> suffix_it(cache.comm_mat, suffix),
                    suffix_end = SparseMatrixInnerIterator<EqType>::makeEnd(cache.comm_mat, suffix);
                  suffix_it != suffix_end; ++suffix_it) {
                    if(*suffix_it != EqType(true)) continue;
                    if(prefix_it.inner() == prefix && suffix_it.inner() == suffix) continue;
                    Path rpath = path_concat(cache.all_paths[prefix_it.inner()], cache.all_paths[suffix_it.inner()]);
                    unsigned rpath_id = cache.path_ids[rpath];
                    if(result.coeff(p, rpath_id) == EqType(false)) {
                        result.insert(p, rpath_id) = EqType(true);
                        result.insert(rpath_id, p) = EqType(true);
                    }
                    assert(result.coeff(p, rpath_id) == EqType(true));
                }
            }
        }
    }

    result.makeCompressed();
    cache.comm_mat = result;
}

void transitivelyCloseCache(CommutationCache& cache) {
    fastpow_into(cache.comm_mat, cache.comm_mat, cache.d.nb_nodes);
}

void closeCache(CommutationCache& cache) {
    for(unsigned i = 0; i < cache.d.nb_nodes; ++i) {
        cache.comm_mat = cache.comm_mat * cache.comm_mat;
        contextCloseCache(cache);
    }
}

void queryGraph(const Diagram& d) {
    auto start_time = std::chrono::high_resolution_clock::now();
    CommutationCache cache = mkCmCache(d, 2);
    auto end_time = std::chrono::high_resolution_clock::now();
    std::cout << "Cache initialized in "
              << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    start_time = std::chrono::high_resolution_clock::now();
    contextCloseCache(cache);
    end_time = std::chrono::high_resolution_clock::now();
    std::cout << "Cache context closure calculated in "
              << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    start_time = std::chrono::high_resolution_clock::now();
    transitivelyCloseCache(cache);
    end_time = std::chrono::high_resolution_clock::now();
    std::cout << "Cache transitive closure calculated in "
              << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

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
    Diagram d;
    d.nb_nodes = 5;
    d.edges.push_back(Arrow(2, 3, "f"));    // 0
    d.edges.push_back(Arrow(1, 3, "g"));    // 1
    d.edges.push_back(Arrow(0, 3, "h"));    // 2
    d.edges.push_back(Arrow(0, 1, "pi1"));  // 3
    d.edges.push_back(Arrow(4, 1, "fpi1")); // 4
    d.edges.push_back(Arrow(0, 2, "pi2"));  // 5
    d.edges.push_back(Arrow(4, 2, "fpi2")); // 6
    d.edges.push_back(Arrow(4, 0, "uniq")); // 7
    addEq(d, mkPath(d, 2), mkPath2(d, 3, 1));
    addEq(d, mkPath(d, 2), mkPath2(d, 5, 0));
    addEq(d, mkPath(d, 4), mkPath2(d, 7, 3));
    addEq(d, mkPath(d, 6), mkPath2(d, 7, 5));
    queryGraph(d);

    return 0;
}
