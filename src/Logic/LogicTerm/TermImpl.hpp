#ifndef TermImpl_HPP
#define TermImpl_HPP
#include "../Logic.hpp"
namespace logicbase {
class TermImpl : public TermInterface {
private:
  static unsigned long long getMax(const std::vector<TermInterface> &terms) {
    unsigned long long max = 0;
    for (auto &term : terms) {
      max = std::max(max, term.getDepth());
    }
    return max + 1;
  }

protected:
  Logic *lb = nullptr;
  long long id;
  unsigned long long depth;
  std::string name;

  OpType opType;
  bool value;
  int i_value;
  double f_value;
  unsigned long long bv_value;
  short bv_size;
  std::vector<TermInterface> nodes;

  CType c_type;

  explicit TermImpl(bool v)
      : lb(nullptr), id(0), depth(0), name(""), opType(OpType::Constant),
        value(v), i_value(0), f_value(0), c_type(CType::BOOL) {}

  explicit TermImpl(int v)
      : lb(nullptr), id(0), depth(0), name(""), opType(OpType::Constant),
        value(v), i_value(v), f_value(0), c_type(CType::INT) {}

  explicit TermImpl(double v)
      : lb(nullptr), id(0), depth(0), name(""), opType(OpType::Constant),
        value(v), i_value(0), f_value(v), c_type(CType::REAL) {}

  explicit TermImpl(unsigned long long v, short bv_size)
      : lb(nullptr), id(0), depth(0), name(""), opType(OpType::Constant),
        value(v), i_value(0), f_value(0), bv_value(v), bv_size(bv_size),
        c_type(CType::BITVECTOR) {}

  explicit TermImpl(Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(std::to_string(id)),
        opType(OpType::Variable), value(false), i_value(0), f_value(0),
        c_type(CType::BOOL) {}

  explicit TermImpl(const std::string &name, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(name),
        opType(OpType::Variable), value(false), i_value(0), f_value(0),
        c_type(CType::BOOL) {}

  explicit TermImpl(OpType opType, const std::string &name, CType cType,
                    Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(name), opType(opType),
        value(false), i_value(0), f_value(0), c_type(cType) {}

  explicit TermImpl(const std::string &name, long long id, Logic *lb = nullptr)
      : lb(lb), id(id), depth(0), name(name), opType(OpType::Variable),
        value(false), i_value(0), f_value(0), c_type(CType::BOOL) {}

  explicit TermImpl(CType cType, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(std::to_string(id)),
        opType(OpType::Variable), value(false), i_value(0), f_value(0),
        c_type(cType) {}

  explicit TermImpl(const char *name, CType cType, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(name),
        opType(OpType::Variable), value(false), i_value(0), f_value(0),
        c_type(cType) {}

  explicit TermImpl(const std::string &name, CType cType, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(0), name(name),
        opType(OpType::Variable), value(false), i_value(0), f_value(0),
        c_type(cType) {}

  explicit TermImpl(const std::string &name, long long id, CType cType,
                    Logic *lb = nullptr)
      : lb(lb), id(id), depth(0), name(name), opType(OpType::Variable),
        value(false), i_value(0), f_value(0), c_type(cType) {}

  explicit TermImpl(OpType ot, const std::initializer_list<TermInterface> &n,
                    CType cType = CType::BOOL, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(getMax(n)), name(getStrRep(ot)),
        opType(ot), nodes(n), c_type(cType) {}

  explicit TermImpl(OpType ot, const std::vector<TermInterface> &n,
                    CType cType = CType::BOOL, Logic *lb = nullptr)
      : lb(lb), id(getNextId(lb)), depth(getMax(n)), name(getStrRep(ot)),
        opType(ot), nodes(n), c_type(cType) {}

public:
  static long long getNextId(Logic *lb = nullptr) {
    if (lb == nullptr)
      return gid++;
    else
      return lb->getNextId();
  }
  std::string getStrRep(OpType opType) const;

  void print(std::ostream &os) const;

  long long getID() const { return id; }

  const std::string &getName() const { return name; }

  OpType getOpType() const { return opType; }

  CType getCType() const { return c_type; }

  const std::vector<TermInterface> &getNodes() const { return nodes; }

  bool getBoolValue() const;

  int getIntValue() const;

  double getFloatValue() const;

  unsigned long long getBitVectorValue() const;

  std::string getValue() const;

  unsigned long long getDepth() const { return depth; }

  bool deepEquals(const TermInterface &other) const;

  Logic *getLogic() const { return lb; }

  static long long gid;
  static long long getGID() { return gid; }

  static void reset() { gid = 0; }
};
};     // namespace logicbase
#endif // LOGICBASE_TERM_IMPL_H