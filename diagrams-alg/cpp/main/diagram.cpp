
#include "diagram.hpp"

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
