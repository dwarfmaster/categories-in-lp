#include "commutation.hpp"

#include "sparse_matrix_iterator.hpp"
#include <chrono>

class PreComposeHook : public CommutationHook {
    unsigned arrow_;
    public:
        PreComposeHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Src; }
        virtual unsigned onSrc() const {
            return cache_.d.edges[arrow_].dst;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1 = consPath(cache_.d, arrow_, cache_.all_paths[p1]);
            Path pth2 = consPath(cache_.d, arrow_, cache_.all_paths[p2]);
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            else return { std::make_pair(it1->second, it2->second) };
        }
};

class PostComposeHook : public CommutationHook {
    unsigned arrow_;
    public:
        PostComposeHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Dst; }
        virtual unsigned onDst() const {
            return cache_.d.edges[arrow_].src;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1 = cache_.all_paths[p1]; pth1.arrows.push_back(arrow_);
            Path pth2 = cache_.all_paths[p2]; pth2.arrows.push_back(arrow_);
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            else return { std::make_pair(it1->second, it2->second) };
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
    std::vector<std::pair<unsigned,unsigned>> oldRanges(connections.size(), std::make_pair(0,0));
    for(size_t size = 1; size < maxSize; ++size) {
        for(size_t cn = 0; cn < connections.size(); ++cn) {
            oldRanges[cn].first = oldRanges[cn].second;
            oldRanges[cn].second = connections[cn].size();
        }
        for(size_t a = 0; a < d.edges.size(); ++a) {
            for(size_t dest = 0; dest < d.nb_nodes; ++dest) {
                unsigned outId = d.edges[a].dst * d.nb_nodes + dest;
                for(size_t old = oldRanges[outId].first; old < oldRanges[outId].second; ++old) {
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

bool unionConnect(CommutationCache& cache, unsigned p1, unsigned p2) {
    unsigned cell1 = unionParent(cache, p1);
    unsigned cell2 = unionParent(cache, p2);
    if(cell1 == cell2) return true;
    if(cache.related_paths[cell1].rank < cache.related_paths[cell2].rank) {
        cache.related_paths[cell1].parent = cell2;
    } else {
        cache.related_paths[cell2].parent = cell1;
        cache.related_paths[cell1].rank +=
            (cache.related_paths[cell1].rank == cache.related_paths[cell2].rank);
    }
    return false;
}

unsigned unionParent(const CommutationCache& cache, unsigned p) {
    if(cache.related_paths[p].parent != p) {
        cache.related_paths[p].parent = unionParent(cache, cache.related_paths[p].parent);
    }
    return cache.related_paths[p].parent;
}

bool unionQuery(const CommutationCache& cache, unsigned p1, unsigned p2) {
    return unionParent(cache, p1) == unionParent(cache, p2);
}

void connectWithHooks(CommutationCache& cache, unsigned p1, unsigned p2) {
    assert(cache.all_paths[p1].src == cache.all_paths[p2].src);
    assert(path_dst(cache.all_paths[p1]) == path_dst(cache.all_paths[p2]));

    std::deque<std::pair<unsigned,unsigned>> queue = { std::make_pair(p1, p2) };
    while(!queue.empty()) {
        auto [p1,p2] = queue.front();
        queue.pop_front();
        if(unionConnect(cache, p1, p2)) continue;

        unsigned src = cache.all_paths[p1].src;
        unsigned dst = path_dst(cache.all_paths[p1]);
        using CT = CommutationHook::ConditionType;
        for(auto it = cache.hooks.begin(), end = cache.hooks.end(); it != end; ++it) {
            switch((*it)->condition()) {
                case CT::Endpoints:
                    if((*it)->onSrc() != src || (*it)->onDst() != dst) continue;
                    break;
                case CT::Dst:
                    if((*it)->onDst() != dst) continue;
                    break;
                case CT::Src:
                    if((*it)->onSrc() != src) continue;
                    break;
                default: continue;
            }
            std::vector<std::pair<unsigned,unsigned>> newEqs = (*it)->extend(p1, p2);
            std::copy(newEqs.begin(), newEqs.end(), std::back_inserter(queue));
        }
    }
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
    result.related_paths.resize(nb_paths);
    for(unsigned p = 0; p < nb_paths; ++p) {
        result.path_ids.insert({ result.all_paths[p], p });
        // Initialize union find
        result.related_paths[p].parent = p;
        result.related_paths[p].rank   = 0;
    }

    for(unsigned arrow = 0; arrow < d.edges.size(); ++arrow) {
        addHook<PostComposeHook>(result, arrow);
        addHook<PreComposeHook> (result, arrow);
    }

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
        connectWithHooks(result, p1, p2);
        entries.push_back(T(p1,p2,EqType(true)));
        entries.push_back(T(p2,p1,EqType(true)));
    }
    result.comm_mat.resize(nb_paths, nb_paths);
    result.comm_mat.setFromTriplets(entries.begin(), entries.end());

    return result;
}

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

CommutationCache buildCmCache(std::string_view prefix, std::ostream& os, const Diagram& d, unsigned cost) {
    auto start_time = std::chrono::high_resolution_clock::now();
    CommutationCache cache = mkCmCache(d, 2);
    auto end_time = std::chrono::high_resolution_clock::now();
    os << "[" << prefix << "] Cache initialized in "
       << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    start_time = std::chrono::high_resolution_clock::now();
    contextCloseCache(cache);
    end_time = std::chrono::high_resolution_clock::now();
    os << "[" << prefix << "] Cache context closure calculated in "
       << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    start_time = std::chrono::high_resolution_clock::now();
    transitivelyCloseCache(cache);
    end_time = std::chrono::high_resolution_clock::now();
    os << "[" << prefix << "] Cache transitive closure calculated in "
       << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    return cache;
}

bool cacheQuery(const CommutationCache& cache, unsigned p1, unsigned p2) {
    return cache.comm_mat.coeff(p1, p2);
}
