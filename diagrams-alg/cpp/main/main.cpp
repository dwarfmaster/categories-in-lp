#include <iostream>
#include <vector>
#include <string>
#include <cassert>
#include <span>
#include <chrono>
#include <Eigen/Sparse>

#include "absl/container/flat_hash_map.h"
#include "absl/types/span.h"

#include "eq_type.hpp"
#include "sparse_matrix_iterator.hpp"
#include "diagram.hpp"
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
