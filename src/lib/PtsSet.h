#ifndef ANDERSEN_PTSSET_H
#define ANDERSEN_PTSSET_H

#include <vector>

class AndersPtsSet {
private:
  std::vector<bool> _bitvec;

public:

  AndersPtsSet() = default;
  AndersPtsSet(const AndersPtsSet &S) : _bitvec(S._bitvec) {}
  ~AndersPtsSet() = default;

  const bool has(std::size_t idx) const {
    return idx < _bitvec.size() ? _bitvec[idx] : false;
  }

  bool insert(std::size_t idx) {
    bool ret;
    if (idx < _bitvec.size()) {
      ret = !_bitvec[idx];
    } else {
      _bitvec.resize(idx + 1);
      ret = true;
    }
    _bitvec[idx] = true;
    return ret;
  }

  std::size_t insert(AndersPtsSet &S) {
    std::size_t ret = 0;
    if (S.getSize() > _bitvec.size()) {
      _bitvec.resize(S.getSize());
    }
    for (std::size_t i = 0; i < S.getSize(); ++i) {
      if (S._bitvec[i] && !_bitvec[i]) {
        ret += 1;
        _bitvec[i] = true;
      }
    }
    return ret;
  }

  void reset(std::size_t idx) {
    _bitvec[idx] = false;
  }

  void clear() {
    _bitvec.clear();
  }

  std::size_t getSize() const {
    return _bitvec.size();
  }

  bool isEmpty() const {
    return _bitvec.empty();  // Always prefer using this function to perform empty test
  }

  // iterator begin() { return _bitvec.begin(); }
  // iterator end() { return _bitvec.end(); }
  // const_iterator begin() const { return _bitvec.begin(); }
  // const_iterator end() const { return _bitvec.end(); }

  std::size_t find_first() const {
    if (_bitvec.empty()) return -1;
    return std::find(_bitvec.begin(), _bitvec.end(), true) - _bitvec.begin();
  }

  std::size_t find_next(std::size_t last) const {
    if (_bitvec.empty()) return -1;
    auto ret = (std::find(_bitvec.begin() + last + 1, _bitvec.end(), true) - _bitvec.begin());
    return ret == 0 ? _bitvec.size() : ret;
  }
};

#endif //ANDERSEN_PTSSET_H
