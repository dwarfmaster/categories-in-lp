
#include "diagram.hpp"

// Returns true if already normal
bool Path::normalize() {
    bool changed = false;
    unsigned size = arrows.size();
    while(true) {
        unsigned in = 0, out = 0;
        while(in + 1 < size) {
            if(diag->edges[arrows[in]].inverse == arrows[in+1]) {
                in += 2;
                changed = true;
            } else {
                arrows[out] = arrows[in];
                ++in; ++out;
            }
        }
        // Copy the last element if it hasn't been skipped
        if(in + 1 == arrows.size()) {
            arrows[out] = arrows[in];
            ++in; ++out;
        }
        if(size == out) break;
        else size = out;
    }
    arrows.resize(size);
    return !changed;
}

void Path::precompose(unsigned arrow) {
    if(arrows.empty() || diag->edges[arrows.back()].inverse != arrow) {
        arrows.push_back(arrow);
    } else {
        arrows.resize(arrows.size() - 1);
    }
}

void Path::precompose(const Path& p) {
    unsigned pstart = 0, last = arrows.size();
    while(last > 0 && pstart < p.arrows.size()) {
        --last;
        if(diag->edges[arrows[last]].inverse != p.arrows[pstart]) break;
        ++pstart;
    }
    arrows.resize(last + p.arrows.size() - pstart);
    for(size_t i = pstart; i < p.arrows.size(); ++i) arrows[(last + i) - pstart] = p.arrows[i];
}

void Path::postcompose(unsigned arrow) {
    if(arrows.empty() || diag->edges[arrows[0]].inverse != arrow) {
        arrows.resize(arrows.size() + 1);
        if(arrows.empty()) {
            arrows = { arrow };
        } else {
          for (size_t i = arrows.size() - 1; i > 0; --i) arrows[i] = arrows[i-1];
          arrows[0] = arrow;
        }
    } else {
        for(size_t i = 0; i + 1 < arrows.size(); ++i) arrows[i] = arrows[i+1];
        arrows.resize(arrows.size() - 1);
    }
}

void Path::postcompose(const Path& p) {
    Path temp = p; temp.precompose(*this);
    *this = std::move(temp);
}

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
        os << "id_" << p.src;
        return os;
    }
    for(auto it = p.arrows.rbegin(), end = p.arrows.rend(); it != end; ++it) {
        os << p.diag->edges[*it].name;
        if(it + 1 != end) os << " o ";
    }
    return os;
}

void addEq(Diagram& d, const Path& p1, const Path& p2) {
    assert(p1.diag == std::addressof(d));
    assert(p2.diag == std::addressof(d));
    assert(p1.src == p2.src);
    assert(path_dst(p1) == path_dst(p2));
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
