#include <iostream>
#include <vector>
#include <string>
#include <cassert>
#include <Eigen/Sparse>

#include "absl/container/flat_hash_map.h"

#include "eq_type.hpp"
#include "sparse_matrix_iterator.hpp"

struct Arrow {
    unsigned src, dst;
    std::string name;
    Arrow(unsigned s, unsigned d, const std::string& n) : src(s), dst(d), name(n) {}
};

struct Path {
    unsigned src;
    std::vector<unsigned> arrows;

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

void addEq(Diagram& d, const Path& p1, const Path& p2) {
    d.faces.push_back(std::make_pair(p1, p2));
}
void addEq(Diagram& d, Path&& p1, Path&& p2) {
    d.faces.push_back(std::make_pair(p1, p2));
}

Path mkPath(const Diagram& d, unsigned arrow) {
    return { d.edges[arrow].src, { arrow } };
}
Path mkPath2(const Diagram& d, unsigned a1, unsigned a2) {
    assert(d.edges[a1].dst == d.edges[a2].src);
    return {d.edges[a1].src, { a1, a2 }};
}
Path consPath(const Diagram& d, unsigned arrow, const Path& p) {
    assert(d.edges[arrow].dst == p.src);
    std::vector<unsigned> steps;
    steps.resize(p.arrows.size() + 1);
    steps[0] = arrow;
    std::copy(p.arrows.begin(), p.arrows.end(), steps.begin() + 1);
    return { d.edges[arrow].src, steps };
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

using EqMat = Eigen::SparseMatrix<EqType>;
struct CommutationCache {
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
    addEq(d, mkPath(d, 7), mkPath2(d, 4, 1));
    addEq(d, mkPath(d, 7), mkPath2(d, 5, 0));

    CommutationCache cache = mkCmCache(d, 2);
    std::cout << "All paths[" << cache.all_paths.size() << "]:\n";
    for(const Path& p : cache.all_paths) {
        std::cout << "  - ";
        if(p.arrows.empty()) {
            std::cout << "id_" << p.src << "\n";
            continue;
        }
        for(auto it = p.arrows.rbegin(), end = p.arrows.rend(); it != end; ++it) {
            std::cout << d.edges[*it].name;
            if(it + 1 != end) std::cout << " o ";
        }
        std::cout << "\n";
    }
    std::cout << std::endl;

    std::cout << "Initial equalities : ";
    CompressedSparseMatrixIterator<EqType> it(cache.comm_mat);
    unsigned count = 0;
    for(CompressedSparseMatrixIterator<EqType> it(cache.comm_mat), end(CompressedSparseMatrixIterator<EqType>::makeEnd(cache.comm_mat)); it != end; ++it) {
        std::cout << it.coordinates().first << "x" << it.coordinates().second << " ";
        ++count;
    }
    std::cout << "(" << count << ")" << std::endl;
    std::cout << cache.comm_mat << std::endl;

    return 0;
}
