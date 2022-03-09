#ifndef DEF_COMMUTATION
#define DEF_COMMUTATION

#include <vector>
#include <string>
#include <iostream>
#include "absl/container/flat_hash_map.h"
#include "diagram.hpp"

struct CommutationCache;
class CommutationHook {
    protected:
        const CommutationCache& cache_;

    public:
        CommutationHook(const CommutationCache& cache) : cache_(cache) {}

        enum class ConditionType { Src, Dst, Endpoints };
        virtual ConditionType condition() const = 0;
        virtual unsigned onSrc() const { return 0; }
        virtual unsigned onDst() const { return 0; }

        virtual std::vector<std::pair<unsigned,unsigned>> extend(unsigned p1, unsigned p2) = 0;
};

inline bool operator<(std::pair<unsigned, unsigned> endps, std::shared_ptr<CommutationHook> hook) {
    return endps < std::make_pair(hook->onSrc(), hook->onDst());
}
inline bool operator<(std::shared_ptr<CommutationHook> hook, std::pair<unsigned, unsigned> endps) {
    return std::make_pair(hook->onSrc(), hook->onDst()) < endps;
}
inline bool operator<(unsigned endp, std::shared_ptr<CommutationHook> hook) {
    if(hook->condition() == CommutationHook::ConditionType::Src) return endp < hook->onSrc();
    else return endp < hook->onDst();
}
inline bool operator<(std::shared_ptr<CommutationHook> hook, unsigned endp) {
    if(hook->condition() == CommutationHook::ConditionType::Src) return hook->onSrc() < endp;
    else return hook->onDst() < endp;
}
inline bool operator<(std::shared_ptr<CommutationHook> hook1, std::shared_ptr<CommutationHook> hook2) {
    using CT = CommutationHook::ConditionType;
    if(hook1->condition() == CT::Src && hook2->condition() == CT::Src) return hook1->onSrc() < hook2->onSrc();
    else if(hook1->condition() == CT::Dst && hook2->condition() == CT::Dst) return hook1->onDst() < hook2->onDst();
    else if(hook1->condition() == CT::Endpoints && hook2->condition() == CT::Endpoints) {
        return std::make_pair(hook1->onSrc(), hook1->onDst())
            < std::make_pair(hook2->onSrc(), hook2->onDst());
    } else return hook1->condition() < hook2->condition();
}

struct CommutationCache {
    Diagram d;
    std::vector<Path> all_paths;
    absl::flat_hash_map<Path,unsigned> path_ids;

    struct UnionCell {
        unsigned parent, rank;
    };
    mutable std::vector<UnionCell> related_paths;
    std::vector<std::shared_ptr<CommutationHook>> hooks;
};

template<typename Hook, typename... Args>
void addHook(CommutationCache& cache, Args... args) {
    std::shared_ptr<Hook> hook = std::make_shared<Hook>(cache, args...);
    cache.hooks.push_back(hook);
}

std::vector<Path> enumeratePathsOfSize(const Diagram& d, size_t maxSize);
// Returns true if p1 and p2 were already connected
bool unionConnect(CommutationCache& cache, unsigned p1, unsigned p2);
unsigned unionParent(const CommutationCache& cache, unsigned p);

// Add equality and run hooks to recursivaly add more equalities
void connectWithHooks(CommutationCache& cache, unsigned p1, unsigned p2);

// cost is a number that constrain the solver, since the problem in undecidable
// in general
CommutationCache mkCmCache(const Diagram& d, unsigned cost);
// Precompute everything, printing timestamps of operations on os
CommutationCache buildCmCache(std::string_view prefix, std::ostream& os, const Diagram& d, unsigned cost);

// Query cache for equality of path
bool cacheQuery(const CommutationCache& cache, unsigned p1, unsigned p2);

#endif // DEF_COMMUTATION
