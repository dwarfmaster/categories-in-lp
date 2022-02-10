#ifndef DEF_EQ_TYPE
#define DEF_EQ_TYPE

#include <Eigen/Core>

class EqType {
    bool b;

    public:
        EqType(bool bl) : b(bl) {}
        operator bool() const { return b; }

        // The real operators
        inline EqType& operator+=(const EqType& t) {
            b = b || t.b;
            return *this;
        }
        inline EqType& operator*=(const EqType& t) {
            b = b && t.b;
            return *this;
        }
        // Fake operators, with no real semantic
        inline EqType& operator-=(const EqType& t) {
            b = t.b ? !b : b;
            return *this;
        }
        inline EqType& operator/=(const EqType&) { return *this; }
};

inline EqType operator+(const EqType& t1, const EqType& t2) { EqType ret(t1); ret += t2; return ret; }
inline EqType operator*(const EqType& t1, const EqType& t2) { EqType ret(t1); ret *= t2; return ret; }
inline EqType operator-(const EqType& t1, const EqType& t2) { EqType ret(t1); ret -= t2; return ret; }
inline EqType operator/(const EqType& t1, const EqType& t2) { EqType ret(t1); ret /= t2; return ret; }

namespace Eigen {
    template <> struct NumTraits<EqType> : GenericNumTraits<EqType> {
        using Real = EqType;
        using NonInteger = EqType;
        using Nested = EqType;

        static inline Real epsilon() { return EqType(false); }
        static inline Real dummy_precision() { return EqType(false); }
        static inline int digits10() { return 0; }

        enum {
          IsInteger = 1,
          IsSigned = 0,
          IsComplex = 0,
          RequireInitialization = 0,
          ReadCost = 1,
          AddCost = 3,
          MulCost = 3
        };
    };
}

#endif // DEF_EQ_TYPE
