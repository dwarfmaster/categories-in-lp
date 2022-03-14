#include "diagram_builder.hpp"

unsigned DiagramBuilder::lookup(std::string_view name) {
    auto it = arrows_.find(name);
    assert(it != arrows_.end());
    return it->second;
}

Path DiagramBuilder::addToPath(Path&& path, unsigned arrow) {
    Path ret(path);
    ret.arrows.push_back(arrow);
    return ret;
}

DiagramBuilder::DiagramBuilder() {
    diag_.nb_nodes = 0;
}

Diagram DiagramBuilder::build() const { return diag_; }

void DiagramBuilder::addNode(const std::string& name) {
    points_.insert(std::make_pair(name, diag_.nb_nodes));
    ++diag_.nb_nodes;
}

unsigned DiagramBuilder::addArrow(const std::string& name, unsigned src, unsigned dst, bool mono, bool epi) {
    unsigned id = diag_.edges.size();
    arrows_.insert(std::make_pair(name, id));
    diag_.edges.push_back(Arrow(src, dst, name));
    diag_.edges.back().isMono = mono;
    diag_.edges.back().isEpi  = epi;
    return id;
}

unsigned DiagramBuilder::addArrow(const std::string& name, const std::string& src, const std::string& dst, bool mono, bool epi) {
    return addArrow(name, points_[src], points_[dst], mono, epi);
}

void DiagramBuilder::makeInverse(unsigned a1, unsigned a2) {
    diag_.edges[a1].isMono = diag_.edges[a1].isEpi = diag_.edges[a1].isIso = true;
    diag_.edges[a2].isMono = diag_.edges[a2].isEpi = diag_.edges[a2].isIso = true;
    diag_.edges[a1].inverse = a2;
    diag_.edges[a2].inverse = a1;
}

void DiagramBuilder::makeInverse(const std::string& a1, const std::string& a2) {
    makeInverse(points_[a1], points_[a2]);
}

std::pair<unsigned,unsigned> DiagramBuilder::addIso(const std::string& name, unsigned src, unsigned dst) {
    unsigned direct = addArrow(name, src, dst, true, true);
    unsigned inverse = addArrow(name + "^-1", dst, src, true, true);
    makeInverse(direct, inverse);
    return std::make_pair(direct, inverse);
}

std::pair<unsigned,unsigned> DiagramBuilder::addIso(const std::string& name, const std::string& src, const std::string& dst) {
    return addIso(name, points_[src], points_[dst]);
}

void DiagramBuilder::addFace(const Path& p1, const Path& p2) {
    ::addEq(diag_, p1, p2);
}

Path DiagramBuilder::emptyPath(const std::string& name) {
    Path p;
    p.diag = &diag_;
    p.src = points_[name];
    return p;
}
