#include "commutation.hpp"

#include <chrono>

class PostComposeHook : public CommutationHook {
    unsigned arrow_;
    public:
        PostComposeHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Src; }
        virtual unsigned onSrc() const {
            return cache_.d.edges[arrow_].dst;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1(cache_.all_paths[p1]); pth1.postcompose(arrow_);
            Path pth2(cache_.all_paths[p2]); pth2.postcompose(arrow_);
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            else return { std::make_pair(it1->second, it2->second) };
        }
};

class PreComposeHook : public CommutationHook {
    unsigned arrow_;
    public:
        PreComposeHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Dst; }
        virtual unsigned onDst() const {
            return cache_.d.edges[arrow_].src;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1(cache_.all_paths[p1]); pth1.precompose(arrow_);
            Path pth2(cache_.all_paths[p2]); pth2.precompose(arrow_);
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            else return { std::make_pair(it1->second, it2->second) };
        }
};

class MonomorphismHook : public CommutationHook {
    unsigned arrow_;
    public:
        MonomorphismHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Dst; }
        virtual unsigned onDst() const {
            return cache_.d.edges[arrow_].dst;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1(cache_.all_paths[p1]);
            Path pth2(cache_.all_paths[p2]);
            if(pth1.arrows.empty() || pth1.arrows.back() != arrow_) return { };
            if(pth2.arrows.empty() || pth2.arrows.back() != arrow_) return { };
            pth1.arrows.pop_back();
            pth2.arrows.pop_back();
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            return { std::make_pair(it1->second, it2->second) };
        }
};

class EpimorphismHook : public CommutationHook {
    unsigned arrow_;
    public:
        EpimorphismHook(const CommutationCache& cache, unsigned arrow)
            : CommutationHook(cache), arrow_(arrow) { }
        virtual ConditionType condition() const { return ConditionType::Src; }
        virtual unsigned onSrc() const {
            return cache_.d.edges[arrow_].src;
        }
        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) {
            Path pth1(cache_.all_paths[p1]);
            Path pth2(cache_.all_paths[p2]);
            if(pth1.arrows.empty() || pth1.arrows[0] != arrow_) return { };
            if(pth2.arrows.empty() || pth2.arrows[0] != arrow_) return { };
            pth1.src = cache_.d.edges[pth1.arrows[0]].dst;
            pth1.arrows.erase(pth1.arrows.begin());
            pth2.src = cache_.d.edges[pth2.arrows[0]].dst;
            pth2.arrows.erase(pth2.arrows.begin());
            auto it1 = cache_.path_ids.find(pth1);
            auto it2 = cache_.path_ids.find(pth2);
            if(it1 == cache_.path_ids.end() || it2 == cache_.path_ids.end()) return { };
            return { std::make_pair(it1->second, it2->second) };
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
                    Path npath(connections[outId][old]); npath.postcompose(a);
                    if(npath.arrows.size() == size + 1) {
                        connections[d.edges[a].src * d.nb_nodes + dest].push_back(npath);
                    }
                }
            }
        }
    }

    // Concatenate all results
    size_t finalSize = 0;
    for(size_t i = 0; i < connections.size(); ++i) finalSize += connections[i].size();
    result.resize(finalSize);
    auto it = result.begin();
    for(size_t i = 0; i < connections.size(); ++i) {
        it = std::copy(std::make_move_iterator(connections[i].begin()),
                       std::make_move_iterator(connections[i].end()),
                       it);
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
        if(d.edges[arrow].isMono) addHook<MonomorphismHook>(result, arrow);
        if(d.edges[arrow].isEpi)  addHook<EpimorphismHook> (result, arrow);
    }

    // Fill pre-existing faces
    for(unsigned f = 0; f < d.faces.size(); ++f) {
        unsigned p1 = result.path_ids[d.faces[f].first];
        unsigned p2 = result.path_ids[d.faces[f].second];
        connectWithHooks(result, p1, p2);
    }

    return result;
}

CommutationCache buildCmCache(std::string_view prefix, std::ostream& os, const Diagram& d, unsigned cost) {
    auto start_time = std::chrono::high_resolution_clock::now();
    CommutationCache cache = mkCmCache(d, cost);
    auto end_time = std::chrono::high_resolution_clock::now();
    os << "[" << prefix << "] Cache initialized in "
       << std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time).count() << "μs" << std::endl;

    return cache;
}

bool cacheQuery(const CommutationCache& cache, unsigned p1, unsigned p2) {
    return unionParent(cache, p1) == unionParent(cache, p2);
}
