#ifndef DEF_DIAGRAM_BUILDER
#define DEF_DIAGRAM_BUILDER

#include "diagram.hpp"
#include "absl/container/flat_hash_map.h"
#include <unordered_map>
#include <string>

class DiagramBuilder {
    Diagram diag_;
    absl::flat_hash_map<std::string, unsigned> points_;
    absl::flat_hash_map<std::string, unsigned> arrows_;

    unsigned lookup(absl::string_view name);
    Path addToPath(Path&& path, unsigned arrow);

    template<typename T> struct PathGetter { };

    public:
        DiagramBuilder();
        Diagram build() const;

        // Low-level edition
        void addNode(const std::string& name);
        unsigned addArrow(const std::string& name, unsigned src, unsigned dst, bool mono = false, bool epi = false);
        unsigned addArrow(const std::string& name, const std::string& src, const std::string& dst, bool mono = false, bool epi = false);
        void makeInverse(unsigned a1, unsigned a2);
        void makeInverse(const std::string& a1, const std::string& a2);
        std::pair<unsigned,unsigned> addIso(const std::string& name, unsigned src, unsigned dst);
        std::pair<unsigned,unsigned> addIso(const std::string& name, const std::string& src, const std::string& dst);
        void addFace(const Path& p1, const Path& p2);

        // Path creation
        Path emptyPath(const std::string& name);
        template<typename... Args>
        struct PathMaker { };
        template<typename... Args>
        Path mkPath(Args... args) {
            return PathMaker<Args...>::make(*this, args...);
        }
        template<typename... Args>
        struct CompMaker { };
        template<typename... Args>
        Path comp(Args... args) {
            return CompMaker<Args...>::make(*this, args...);
        }
};

// Path getters
template<> struct DiagramBuilder::PathGetter<std::string> {
    static unsigned get(DiagramBuilder& db, std::string_view name) { return db.lookup(name); }
};
template<> struct DiagramBuilder::PathGetter<const std::string&> {
    static unsigned get(DiagramBuilder& db, std::string_view name) { return db.lookup(name); }
};
template<> struct DiagramBuilder::PathGetter<const char*> {
    static unsigned get(DiagramBuilder& db, std::string_view name) { return db.lookup(name); }
};
template<> struct DiagramBuilder::PathGetter<unsigned> {
    static unsigned get(DiagramBuilder&, unsigned i) { return i; }
};

// Path makers
template<typename T, typename... Args>
struct DiagramBuilder::PathMaker<T, Args...> {
    static Path make(DiagramBuilder& db, Args... args, T name) {
        return db.addToPath(PathMaker<Args...>::make(db, args...), PathGetter<T>::get(db, name));
    }
};
template<typename T>
struct DiagramBuilder::PathMaker<T> {
    static Path make(DiagramBuilder& db, T name) { return ::mkPath(db.diag_, PathGetter<T>::get(db, name)); }
};
template<typename T, typename... Args>
struct DiagramBuilder::CompMaker<T, Args...> {
    static Path make(DiagramBuilder& db, T name, Args... args) {
        return db.addToPath(CompMaker<Args...>::make(db, args...), PathGetter<T>::get(db, name));
    }
};
template <typename T>
struct DiagramBuilder::CompMaker<T> {
    static Path make(DiagramBuilder& db, T name) {
        return ::mkPath(db.diag_, PathGetter<T>::get(db, name));
    }
};

#endif // DEF_DIAGRAM_BUILDER
