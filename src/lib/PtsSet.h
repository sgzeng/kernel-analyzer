#ifndef ANDERSEN_PTSSET_H
#define ANDERSEN_PTSSET_H

#include <vector>

class AndersPtsSet {
private:
  std::vector<bool> _bitvec;

public:
  using iterator = std::vector<bool>::iterator;
  using const_iterator = std::vector<bool>::const_iterator;

  AndersPtsSet() = default;
  ~AndersPtsSet() = default;

  const bool has(unsigned idx) const {
    return _bitvec.size() < idx ? _bitvec.at(idx) : false;
  }

  bool insert(unsigned idx) {
    bool ret = _bitvec.size() < idx ? _bitvec.at(idx) : false;
    _bitvec[idx] = true;
    return ret;
  }

  bool insert(iterator b, iterator e) {
    bool ret = false;
    for (iterator i = b; i != e; ++i) {
      ret |= *i;
      *i = true;
    }
    return ret;
  }

  void reset(unsigned idx) {
    _bitvec[idx] = false;
  }

  void clear() {
    _bitvec.clear();
  }

  size_t getSize() const {
    return _bitvec.size();
  }

  bool isEmpty() const {
    return _bitvec.empty();  // Always prefer using this function to perform empty test
  }

  iterator begin() { return _bitvec.begin(); }
  iterator end() { return _bitvec.end(); }
  const_iterator begin() const { return _bitvec.begin(); }
  const_iterator end() const { return _bitvec.end(); }

  const_iterator find_first() const {
    return std::find(_bitvec.begin(), _bitvec.end(), true);
  }

  const_iterator find_next(const_iterator last) const {
    return std::find(last + 1, _bitvec.end(), true);
  }
};

#endif //ANDERSEN_PTSSET_H
