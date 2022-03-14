
#include <gtest/gtest.h>
#include <fstream>

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

TEST(Paths, Normalisation) {
  DiagramBuilder db;
  unsigned a = db.addNode("a");
  unsigned b = db.addNode("b");
  unsigned c = db.addNode("c");
  unsigned d = db.addNode("d");
  auto [i1, i1_inv] = db.addIso("i1", a, b);
  auto [i2, i2_inv] = db.addIso("i2", b, c);
  auto [i3, i3_inv] = db.addIso("i3", c, d);
  Diagram diag = db.build();

  Path p1; p1.src = a; p1.diag = &diag; p1.arrows = { i1, i2, i2_inv, i1_inv };
  ASSERT_FALSE(p1.normalize());
  ASSERT_TRUE(p1.isId());

  Path p2; p2.src = a; p2.diag = &diag; p2.arrows = { i1, i2, i3 };
  ASSERT_TRUE(p2.normalize());

  Path p2_; p2_.src = a; p2_.diag = &diag; p2_.arrows = { i2_inv, i1_inv };
  p2.postcompose(p2_);
  ASSERT_TRUE(p2.arrows.size() == 1);
  ASSERT_TRUE(diag.edges[p2.arrows[0]].name == "i3");
}

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
  d.addFace(d.mkPath("h"), d.mkPath("pi1", "f"));
  d.addFace(d.mkPath("h"), d.mkPath("pi2", "g"));
  d.addFace(d.mkPath("fpi1"), d.mkPath("uniq", "pi1"));
  d.addFace(d.mkPath("fpi2"), d.mkPath("uniq", "pi2"));
  Diagram diag = d.build();
  CommutationCache cache = buildCmCache("pullback", std::cout, diag, 2);

  ASSERT_FALSE(cacheQuery(cache, 0, 1));
  ASSERT_TRUE(cacheQuery(cache, 3, 4));
  ASSERT_TRUE(cacheQuery(cache, 10, 11));
  ASSERT_FALSE(cacheQuery(cache, 9, 10));
  ASSERT_TRUE(cacheQuery(cache, 12, 13));
  ASSERT_TRUE(cacheQuery(cache, 15, 16));
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
    d.addFace(d.mkPath("id x pi2 (m2 o m1)"), d.mkPath("id x pi2 m2", "id x pi2 m1"));
    d.addArrow("ev_s", "pi1 s^pi2 s x pi2 s", "pi1 s");
    d.addArrow("pi1 m1", "pi1 s", "pi1 d1");
    d.addArrow("pi1 m2", "pi1 d1", "pi1 d2");
    d.addArrow("pi1 (m2 o m1)", "pi1 s", "pi1 d2");
    d.addFace(d.mkPath("pi1 (m2 o m1)"), d.mkPath("pi1 m1", "pi1 m2"));
    d.addArrow("[m1] x id_d2", "pi1 s^pi2 s x pi2 d2", "pi1 d1^pi2 d1 x pi2 d2");
    d.addArrow("[m1] x id_d1", "pi1 s^pi2 s x pi2 d1", "pi1 d1^pi2 d1 x pi2 d1");
    d.addArrow("id_d1 x pi2 m2", "pi1 d1^pi2 d1 x pi2 d2", "pi1 d1^pi2 d1 x pi2 d1");
    d.addFace(d.mkPath("[m1] x id_d2", "id_d1 x pi2 m2"), d.mkPath("id x pi2 m2", "[m1] x id_d1"));
    d.addArrow("ev_d1", "pi1 d1^pi2 d1 x pi2 d1", "pi1 d1");
    d.addArrow("[m2] x id", "pi1 d1^pi2 d1 x pi2 d2", "pi1 d2^pi2 d2 x pi2 d2");
    d.addArrow("ev_d2", "pi1 d2^pi2 d2 x pi2 d2", "pi1 d2");
    d.addArrow("[m2 o m1] x id", "pi1 s^pi2 s x pi2 d2", "pi1 d2^pi2 d2 x pi2 d2");
    d.addFace(d.mkPath("[m1] x id_d1", "ev_d1"), d.mkPath("id x pi2 m1", "ev_s", "pi1 m1"));
    d.addFace(d.mkPath("[m2] x id", "ev_d2"), d.mkPath("id_d1 x pi2 m2", "ev_d1", "pi1 m2"));

    Diagram diag = d.build();
    CommutationCache cache = buildCmCache("ExpFunc", std::cout, diag, 5);

    std::cout << cache.all_paths[11] << " = " << cache.all_paths[10] << " ?" << std::endl;
    ASSERT_TRUE(cacheQuery(cache, 35, 36));
    ASSERT_TRUE(cacheQuery(cache, 10, 14));
    ASSERT_TRUE(cacheQuery(cache, 1, 2));
    ASSERT_TRUE(cacheQuery(cache, 10, 12));
    ASSERT_TRUE(cacheQuery(cache, 14, 12));
    ASSERT_TRUE(cacheQuery(cache, 10, 16));
    ASSERT_TRUE(cacheQuery(cache, 24, 25));
    ASSERT_TRUE(cacheQuery(cache, 16, 13));
    ASSERT_TRUE(cacheQuery(cache, 13, 15));
    ASSERT_TRUE(cacheQuery(cache, 15, 11));
    ASSERT_TRUE(cacheQuery(cache, 10, 11));
}

TEST(Commutation, EpiMono) {
  DiagramBuilder d;
  d.addNode("a"); d.addNode("b"); d.addNode("c");
  d.addArrow("epi", "a", "b", false, true);
  d.addArrow("f", "b", "c");
  d.addArrow("g", "b", "c");
  d.addArrow("mono", "c", "d", true, false);
  d.addFace(d.mkPath("epi", "f", "mono"), d.mkPath("epi", "g", "mono"));

  Diagram diag = d.build();
  CommutationCache cache = buildCmCache("EpiMono", std::cout, diag, 3);
  // Tests is f = g
  ASSERT_TRUE(cacheQuery(cache, 11, 12));
}
