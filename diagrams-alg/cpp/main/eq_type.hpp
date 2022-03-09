#ifndef DEF_EQ_TYPE
#define DEF_EQ_TYPE

class EqType {
    bool b;

    public:
        EqType(int n) {
            if(n != 0) b = true;
            else       b = false;
        }
        EqType(bool bl) : b(bl) {}
        EqType() : b(false) {}
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
        inline bool operator==(const EqType& eq) {
            return eq.b == b;
        }
        inline bool operator!=(const EqType& eq) {
            return eq.b != b;
        }
};

inline EqType operator+(const EqType& t1, const EqType& t2) { EqType ret(t1); ret += t2; return ret; }
inline EqType operator*(const EqType& t1, const EqType& t2) { EqType ret(t1); ret *= t2; return ret; }
inline EqType operator-(const EqType& t1, const EqType& t2) { EqType ret(t1); ret -= t2; return ret; }
inline EqType operator/(const EqType& t1, const EqType& t2) { EqType ret(t1); ret /= t2; return ret; }

#endif // DEF_EQ_TYPE
