#ifndef DEF_DIAGRAM_BUILDER
#define DEF_DIAGRAM_BUILDER

#include "diagram.hpp"
#include <unordered_map>
#include <string>

class DiagramBuilder {
    Diagram diag_;
    std::unordered_map<std::string, unsigned> points_;
    std::unordered_map<std::string, unsigned> arrows_;

    unsigned lookup(const std::string& name);
    Path addToPath(Path&& path, unsigned arrow);

    public:
        DiagramBuilder();
        Diagram build() const;

        // Low-level edition
        void addNode(const std::string& name);
        void addArrow(const std::string& name, unsigned src, unsigned dst);
        void addArrow(const std::string& name, const std::string& src, const std::string& dst);
        void addFace(const Path& p1, const Path& p2);

        // Path creation
        Path emptyPath(const std::string& name);
        Path mkPath(const std::string& name);
        Path mkPath(unsigned id);
        template<typename... Args>
        Path mkPath(Args... args, const std::string& name) { return addToPath(mkPath(args...), lookup(name)); }
        template<typename... Args>
        Path mkPath(Args... args, unsigned id) { return addToPath(mkPath(args...), id); }
        Path comp(const std::string& name);
        Path comp(unsigned id);
        template<typename... Args>
        Path comp(const std::string& name, Args... args) { return addToPath(comp(args...), lookup(name)); }
        template<typename... Args>
        Path comp(unsigned id, Args... args) { return addToPath(comp(args...), id); }
};

#endif // DEF_DIAGRAM_BUILDER
