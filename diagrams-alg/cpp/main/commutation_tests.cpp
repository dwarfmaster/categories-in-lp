
#include <gtest/gtest.h>

#include "diagram.hpp"
#include "diagram_builder.hpp"
#include "commutation.hpp"

class NullStream : public std::ostream {
public:
  NullStream() : std::ostream(nullptr) {}
  NullStream(const NullStream&) : std::ostream(nullptr) {}
};
template <typename T>
const NullStream& operator<<(NullStream&& os, const T&) {
    return os;
}
NullStream osnull;

TEST(Commutation, Pullback) {
  DiagramBuilder d;
  d.addNode("a");
  d.addNode("b");
  d.addNode("c");
  d.addNode("d");
  d.addNode("p");
  d.addArrow("f", "b", "d");
  d.addArrow("g", "c", "d");
  d.addArrow("h", "a", "d");
  d.addArrow("pi1", "a", "b");
  d.addArrow("pi2", "a", "c");
  d.addArrow("fpi1", "p", "b");
  d.addArrow("fpi2", "p", "c");
  d.addArrow("uniq", "p", "a");
  d.addFace(d.mkPath("h"), d.mkPath<std::string>("pi1", "f"));
  d.addFace(d.mkPath("h"), d.mkPath<std::string>("pi2", "g"));
  d.addFace(d.mkPath("fpi1"), d.mkPath<std::string>("uniq", "pi1"));
  d.addFace(d.mkPath("fpi2"), d.mkPath<std::string>("uniq", "pi2"));
  Diagram diag = d.build();
  CommutationCache cache = buildCmCache("pullback", osnull, diag, 2);

  ASSERT_FALSE(cacheQuery(cache, 0, 1));
  ASSERT_TRUE(cacheQuery(cache, 3, 4));
  ASSERT_TRUE(cacheQuery(cache, 10, 11));
  ASSERT_FALSE(cacheQuery(cache, 13, 11));
  ASSERT_TRUE(cacheQuery(cache, 20, 21));
  ASSERT_TRUE(cacheQuery(cache, 22, 23));
}

TEST(Commutation, ExpFunct) {
    DiagramBuilder d;
    d.addNode("pi1 s^pi2 s x pi2 d2");
    d.addNode("pi1 s^pi2 s x pi2 d1");
    d.addNode("pi1 s^pi2 s x pi2 s");
    d.addNode("pi1 s");
    d.addNode("pi1 d1");
    d.addNode("pi1 d2");
    d.addNode("pi1 d1^pi2 d1 x pi2 d2");
    d.addNode("pi1 d1^pi2 d1 x pi2 d1");
    d.addNode("pi1 d2^pi2 d2 x pi2 d2");
    d.addArrow("id x pi2 m2", "pi1 s^pi2 s x pi2 d2", "pi1 s^pi2 s x pi2 d1");
    d.addArrow("id x pi2 m1", "pi1 s^pi2 s x pi2 d1", "pi1 s^pi2 s x pi2 s");
    d.addArrow("id x pi2 (m2 o m1)", "pi1 s^pi2 s x pi2 d2", "pi1 s^pi2 s x pi2 s");
    d.addFace(d.mkPath("id x pi2 (m2 o m1)"), d.mkPath<std::string>("id x pi2 m2", "id x pi2 m1"));
    d.addArrow("ev_s", "pi1 s^pi2 s x pi2 s", "pi1 s");
    d.addArrow("pi1 m1", "pi1 s", "pi1 d1");
    d.addArrow("pi1 m2", "pi1 d1", "pi1 d2");
    d.addArrow("pi1 (m2 o m1)", "pi1 s", "pi1 d2");
    d.addFace(d.mkPath("pi1 (m2 o m1)"), d.mkPath<std::string>("pi1 m1", "pi1 m2"));
    d.addArrow("[m1] x id_d2", "pi1 s^pi2 s x pi2 d2", "pi1 d1^pi2 d1 x pi2 d2");
    d.addArrow("[m1] x id_d1", "pi1 s^pi2 s x pi2 d1", "pi1 d1^pi2 d1 x pi2 d1");
    d.addArrow("id_d1 x pi2 m2", "pi1 d1^pi2 d1 x pi2 d2", "pi1 d1^pi2 d1 x pi2 d1");
    d.addFace(d.mkPath<std::string>("[m1] x id_d2", "id_d1 x pi2 m2"), d.mkPath<std::string>("id x pi2 m2", "[m1] x id_d1"));
    d.addArrow("ev_d1", "pi1 d1^pi2 d1 x pi2 d1", "pi1 d1");
    d.addArrow("[m2] x id", "pi1 d1^pi2 d1 x pi2 d2", "pi1 d2^pi2 d2 x pi2 d2");
    d.addArrow("ev_d2", "pi1 d2^pi2 d2 x pi2 d2", "pi1 d2");
    d.addArrow("[m2 o m1] x id", "pi1 s^pi2 s x pi2 d2", "pi1 d2^pi2 d2 x pi2 d2");

}
