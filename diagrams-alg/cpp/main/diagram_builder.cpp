#include "diagram_builder.hpp"

unsigned DiagramBuilder::lookup(const std::string& name) {
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

void DiagramBuilder::addArrow(const std::string& name, unsigned src, unsigned dst) {
    arrows_.insert(std::make_pair(name, diag_.edges.size()));
    diag_.edges.push_back(Arrow(src, dst, name));
}

void DiagramBuilder::addArrow(const std::string& name, const std::string& src, const std::string& dst) {
    addArrow(name, points_[src], points_[dst]);
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

Path DiagramBuilder::mkPath(const std::string& name) { return ::mkPath(diag_, lookup(name)); }
Path DiagramBuilder::mkPath(unsigned id)   { return ::mkPath(diag_, id); }
Path DiagramBuilder::comp(const std::string& name)   { return ::mkPath(diag_, lookup(name)); }
Path DiagramBuilder::comp(unsigned id)     { return ::mkPath(diag_, id); }
