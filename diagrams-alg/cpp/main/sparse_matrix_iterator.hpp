#ifndef DEF_SPARSE_MATRIX_ITERATOR
#define DEF_SPARSE_MATRIX_ITERATOR

#include <Eigen/Sparse>
#include <iterator>

// The matrix must be compressed for it to work
template <typename Scalar>
class CompressedSparseMatrixIterator {
    unsigned id_;
    unsigned size_;
    const Eigen::SparseMatrix<Scalar>& matrix_;

    public:
        using iterator_category = std::input_iterator_tag;
        using value_type = Scalar;
        using pointer    = Scalar*;
        using reference  = const Scalar&;

    public:
        using M = Eigen::SparseMatrix<Scalar>;
        CompressedSparseMatrixIterator(const M& matrix) : id_(0), size_(matrix.outerIndexPtr()[matrix.outerSize()]), matrix_(matrix) {
            assert(matrix.isCompressed());
        }
        CompressedSparseMatrixIterator(const CompressedSparseMatrixIterator& it)
            : id_(it.id_), size_(it.size_), matrix_(it.matrix_) { }
        static CompressedSparseMatrixIterator makeEnd(const M& matrix) {
            CompressedSparseMatrixIterator end(matrix);
            end.id_ = end.size_;
            return end;
        }

        std::pair<unsigned,unsigned> coordinates() const {
            for(unsigned outer = 0; outer < matrix_.outerSize(); ++outer) {
                unsigned outId = matrix_.outerIndexPtr()[outer + 1];
                if(id_ < outId) return std::make_pair(outer, matrix_.innerIndexPtr()[id_]);
            }
            assert(false);
        }

        reference operator*() const {
            return *(matrix_.valuePtr() + id_);
        }
        pointer operator->() const {
            return matrix_.valuePtr() + id_;
        }

        CompressedSparseMatrixIterator& operator++() {
            ++id_;
            if(id_ > size_) id_ = size_;
            return *this;
        }
        CompressedSparseMatrixIterator operator++(int) {
            CompressedSparseMatrixIterator ret(*this);
            ++ret;
            return ret;
        }

        friend bool operator==(const CompressedSparseMatrixIterator& a, const CompressedSparseMatrixIterator& b) {
            return std::addressof(a.matrix_) == std::addressof(b.matrix_) && a.id_ == b.id_;
        }
        friend bool operator!=(const CompressedSparseMatrixIterator& a, const CompressedSparseMatrixIterator& b) {
            return !(a == b);
        }
};

// Matrix must not be compressed
// TODO untested
template <typename Scalar>
class UncompressedSparseMatrixIterator {
    unsigned outerId_;
    unsigned innerId_;
    const Eigen::SparseMatrix<Scalar>& matrix_;

    public:
        using iterator_category = std::input_iterator_tag;
        using value_type = Scalar;
        using pointer    = Scalar*;
        using reference  = const Scalar&;

    public:
        using M = Eigen::SparseMatrix<Scalar>;
        UncompressedSparseMatrixIterator(const M& matrix) : outerId_(0), innerId_(0), matrix_(matrix) {
            assert(!matrix.isCompressed());
        }
        UncompressedSparseMatrixIterator(const UncompressedSparseMatrixIterator& it)
            : outerId_(it.outerId_), innerId_(it.innerId_), matrix_(it.matrix_) { }
        static UncompressedSparseMatrixIterator makeEnd(const M& matrix) {
            UncompressedSparseMatrixIterator end(matrix);
            end.innerId_ = 0;
            end.outerId_ = matrix.outerSize();
            return end;
        }

        unsigned outer() const {
            return outerId_;
        }
        unsigned inner() const {
            return *(matrix_.innerIndexPtr() + innerId_);
        }

        reference operator*() const {
            return *(matrix_.valuePtr() + innerId_);
        }
        pointer operator->() const {
            return matrix_.valuePtr() + innerId_;
        }

        UncompressedSparseMatrixIterator& operator++() {
            unsigned inner_pos = innerId_ - *(matrix_.outerIndexPtr() + outerId_);
            unsigned inner_size = matrix_.innerNonZeroPtr()[outerId_];
            if(inner_pos < inner_size) ++innerId_;
            else if(outerId_ + 1 == matrix_.outerSize()) {
                outerId_ = matrix_.outerSize();
                innerId_ = 0;
            } else {
                ++outerId_;
                innerId_ = matrix_.outerIndexPtr()[outerId_];
            }
            return *this;
        }
        UncompressedSparseMatrixIterator operator++(int) {
            UncompressedSparseMatrixIterator ret(*this);
            ++ret;
            return ret;
        }

        friend bool operator==(const UncompressedSparseMatrixIterator& a, const UncompressedSparseMatrixIterator& b) {
            return std::addressof(a.matrix_) == std::addressof(b.matrix_) && a.outerId_ == b.outerId_ && a.innerId_ == b.innerId_;
        }
        friend bool operator!=(const UncompressedSparseMatrixIterator& a, const UncompressedSparseMatrixIterator& b) {
            return !(a == b);
        }
};

template <typename Scalar>
class SparseMatrixInnerIterator {
    const Scalar* actual_;
    const typename Eigen::SparseMatrix<Scalar>::StorageIndex* index_;

    static unsigned computeInnerSize(const Eigen::SparseMatrix<Scalar>& matrix, unsigned outer) {
        if(matrix.isCompressed()) {
            return matrix.outerIndexPtr()[outer+1] - matrix.outerIndexPtr()[outer];
        } else {
            return matrix.innerNonZeroPtr()[outer];
        }
    }

    public:
        using iterator_category = std::input_iterator_tag;
        using value_type = const Scalar;
        using pointer    = const Scalar*;
        using reference  = const Scalar&;

    public:
        using M = Eigen::SparseMatrix<Scalar>;
        SparseMatrixInnerIterator(const M& matrix, unsigned outer) : actual_(nullptr), index_(nullptr) {
            assert(outer < matrix.outerSize());
            actual_ = matrix.valuePtr() + matrix.outerIndexPtr()[outer];
            index_  = matrix.innerIndexPtr() + matrix.outerIndexPtr()[outer];
        }
        SparseMatrixInnerIterator(const SparseMatrixInnerIterator& it) : actual_(it.actual_), index_(it.index_) { }
        static SparseMatrixInnerIterator makeEnd(const M& matrix, unsigned outer) {
            SparseMatrixInnerIterator end(matrix, outer);
            if(matrix.isCompressed()) {
                end.actual_ = matrix.valuePtr() + matrix.outerIndexPtr()[outer + 1];
            } else {
                end.actual_ += matrix.innerNonZeroPtr()[outer];
            }
            return end;
        }

        unsigned inner() const {
            return *index_;
        }

        reference operator*() const {
            return *actual_;
        }
        pointer operator->() const {
            return actual_;
        }

        SparseMatrixInnerIterator& operator++() {
            ++actual_;
            return *this;
        }
        SparseMatrixInnerIterator operator++(int) {
            SparseMatrixInnerIterator ret(*this);
            ++ret;
            return ret;
        }

        friend bool operator==(const SparseMatrixInnerIterator& a, const SparseMatrixInnerIterator& b) {
            return a.actual_ == b.actual_;
        }
        friend bool operator!=(const SparseMatrixInnerIterator& a, const SparseMatrixInnerIterator& b) {
            return a.actual_ != b.actual_;
        }
};

template <typename Scalar>
bool isSparseMatrixNullAt(const Eigen::SparseMatrix<Scalar>& matrix, unsigned outer, unsigned inner) {
    SparseMatrixInnerIterator<Scalar> it(matrix, outer);
    auto end = SparseMatrixInnerIterator<Scalar>::makeEnd(matrix, outer);
    for(; it != end; ++it) {
        if(it.inner() == inner) return false;
    }
    return true;
}

#endif // DEF_SPARSE_MATRIX_ITERATOR
