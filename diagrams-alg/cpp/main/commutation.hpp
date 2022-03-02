#ifndef DEF_COMMUTATION
#define DEF_COMMUTATION

#include <Eigen/Sparse>
#include <vector>
#include <string>
#include <iostream>
#include "absl/container/flat_hash_map.h"
#include "eq_type.hpp"
#include "diagram.hpp"

struct CommutationCache {
    using EqMat = Eigen::SparseMatrix<EqType>;
    Diagram d;
    std::vector<Path> all_paths;
    absl::flat_hash_map<Path,unsigned> path_ids;
    EqMat comm_mat;
};

std::vector<Path> enumeratePathsOfSize(const Diagram& d, size_t maxSize);

// cost is a number that constrain the solver, since the problem in undecidable
// in general
CommutationCache mkCmCache(const Diagram& d, unsigned cost);

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
void contextCloseCache(CommutationCache& cache);
void transitivelyCloseCache(CommutationCache& cache);

// Precompute everything, printing timestamps of operations on os
CommutationCache buildCmCache(std::string_view prefix, std::ostream& os, const Diagram& d, unsigned cost);

// Query cache for equality of path
bool cacheQuery(const CommutationCache& cache, unsigned p1, unsigned p2);

#endif // DEF_COMMUTATION
