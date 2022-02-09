#ifndef DEF_EQ_TYPE
#define DEF_EQ_TYPE

class EqType {
    bool b;

    public:
        EqType(bool bl) : b(bl) {}
        operator bool() const { return b; }
};

#endif // DEF_EQ_TYPE
