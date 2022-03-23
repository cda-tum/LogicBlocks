#include "LogicBlock/Z3Logic.hpp"
#include "LogicUtil/util_logic.hpp"
#include "utils/util.hpp"

#include <sstream>

namespace z3logic {

expr Z3Base::getExprTerm(unsigned long long id, CType type) {
  if (variables.find(id) == variables.end() ||
      !variables.at(id)[static_cast<int>(type)].first)
    throw std::runtime_error("Variable not found");
  return variables.at(id)[static_cast<int>(type)].second;
}

expr Z3Base::convert(const LogicTerm &a, CType to_type) {
  if (a.getOpType() == OpType::Constant) {
    return convertConstant(a, to_type);
  };
  std::vector<std::pair<bool, expr>> v;
  if (cache.find(a) != cache.end()) {
    v = cache.at(a);
    if (v[static_cast<int>(to_type)].first)
      return v[static_cast<int>(to_type)].second;
  } else {
    for (int i = 0; i < 4; i++) {
      v.push_back(std::make_pair(false, ctx.bool_val(false)));
    }
  }
  switch (a.getOpType()) {
  case OpType::Variable: {
    v[static_cast<int>(to_type)].first = true;
    v[static_cast<int>(to_type)].second = convertVariableTo(a, to_type);
  } break;

  case OpType::AND: {
    expr s = this->ctx.bool_val(true);
    bool alternate = false;
    for (const LogicTerm &lt : a.getNodes()) {
      if (alternate)
        s = s && convert(lt, to_type);
      else
        s = convert(lt, to_type) && s;
      alternate = !alternate;
    }
    v[static_cast<int>(to_type)].second = s.simplify();
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::OR: {
    expr s = this->ctx.bool_val(false);
    bool alternate = false;
    for (const LogicTerm &lt : a.getNodes()) {
      if (alternate)
        s = s || convert(lt, to_type);
      else
        s = convert(lt, to_type) || s;
      alternate = !alternate;
    }

    v[static_cast<int>(to_type)].second = s.simplify();
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::EQ:
    v[static_cast<int>(to_type)].second = convertOperator(
        a.getNodes()[0], a.getNodes()[1], z3::operator==, CType::ERRORTYPE);
    v[static_cast<int>(to_type)].first = true;
    break;
  case OpType::XOR:
    v[static_cast<int>(to_type)].second = convertOperator(
        a.getNodes()[0], a.getNodes()[1], z3::operator!=, CType::ERRORTYPE);
    v[static_cast<int>(to_type)].first = true;
    break;
  case OpType::NEG:
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], z3::operator!, CType::ERRORTYPE);
    v[static_cast<int>(to_type)].first = true;
    break;
  case OpType::ITE:
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], a.getNodes()[1], a.getNodes()[2],
                        z3::ite, CType::ERRORTYPE);
    v[static_cast<int>(to_type)].first = true;
    break;
  case OpType::IMPL:
    v[static_cast<int>(to_type)].second = convertOperator(
        a.getNodes()[0], a.getNodes()[1], z3::implies, CType::BOOL);
    v[static_cast<int>(to_type)].first = true;
    break;
  case OpType::ADD: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator+,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::SUB: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator-,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::MUL: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator*,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::DIV: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator/,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::GT: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator>,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::LT: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator<,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::BIT_AND: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator&, to_type);
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::BIT_OR: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator|,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::BIT_XOR: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes(), z3::operator^,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  case OpType::BIT_EQ: {
    v[static_cast<int>(to_type)].second =
        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator==,
                        logicutil::extractNumberType(a.getNodes()));
    v[static_cast<int>(to_type)].first = true;
  } break;
  default:
    util::fatal("Unsupported operation");
    break;
  }
  cache.insert_or_assign(a, v);
  return cache.at(a)[static_cast<int>(to_type)].second;
}

void Z3LogicBlock::assertFormula(const LogicTerm &a) {
  if (a.getOpType() == OpType::AND) {
    for (const auto &clause : a.getNodes()) {
      clauses.insert(clause);
      if (convertWhenAssert) {
        this->solver.add(convert(clause, CType::BOOL));
      }
    }
  } else {
    clauses.insert(a);
    if (convertWhenAssert) {
      this->solver.add(convert(a, CType::BOOL));
    }
  }
}

void Z3LogicBlock::dumpZ3State(std::ostream &stream) {
  stream << "Z3State: " << std::endl;
  stream << solver << std::endl;
}

void Z3LogicBlock::produceInstance() {
  auto it = clauses.begin();
  while (it != clauses.end()) {
    expr c = ctx.bool_val(false);
    c = convert(*it, CType::BOOL);
    this->solver.add(c);
    ++it;
  }
}

Result Z3LogicBlock::solve() {
  z3::check_result res = this->solver.check();
  if (res == z3::sat) {
    this->model = new Z3Model(this->ctx, this->solver.get_model());
    return Result::SAT;
  }
  return Result::UNSAT;
}

void Z3LogicBlock::internal_reset() {
  variables.clear();
  cache.clear();
}

z3::expr Z3Base::convertVariableTo(const LogicTerm &a, CType to_type) {
  std::vector<std::pair<bool, expr>> v;
  if (variables.find(a.getID()) != variables.end()) {
    v = variables.at(a.getID());
    if (v[static_cast<int>(to_type)].first)
      return v[static_cast<int>(to_type)].second;
  } else {
    for (int i = 0; i < 4; i++) {
      v.push_back(std::make_pair(false, ctx.bool_val(false)));
    }
  }
  v[static_cast<int>(to_type)].first = true;
  switch (a.getCType()) {
  case CType::BOOL:
    v[static_cast<int>(to_type)].second = convertVariableFromBoolTo(a, to_type);
    break;
  case CType::INT:
    v[static_cast<int>(to_type)].second = convertVariableFromIntTo(a, to_type);
    break;
  case CType::REAL:
    v[static_cast<int>(to_type)].second = convertVariableFromRealTo(a, to_type);
    break;
  case CType::BITVECTOR:
    v[static_cast<int>(to_type)].second =
        convertVariableFromBitvectorTo(a, to_type);
    break;
  default:
    util::fatal("Unsupported type");
    break;
  }
  variables.insert_or_assign(a.getID(), v);
  return v[static_cast<int>(to_type)].second;
}
z3::expr Z3Base::convertVariableFromBoolTo(const LogicTerm &a, CType to_type) {
  std::stringstream ss;
  ss << a.getName() << "_" << a.getID();
  switch (to_type) {
  case CType::BOOL:
    return ctx.bool_const(ss.str().c_str());
    break;
  case CType::INT:
    return z3::ite(ctx.bool_const(ss.str().c_str()), ctx.int_val(1),
                   ctx.int_val(0));
    break;
  case CType::REAL:
    return z3::ite(ctx.bool_const(ss.str().c_str()), ctx.real_val(1),
                   ctx.real_val(0));
    break;
  case CType::BITVECTOR:
    return ite(ctx.bool_const(ss.str().c_str()), ctx.bv_val(1, 1),
               ctx.bv_val(0, 1));
    break;
  default:
    util::fatal("Unsupported type");
  }
  util::fatal("Unsupported type");
  return ctx.bool_val(false);
}
z3::expr Z3Base::convertVariableFromIntTo(const LogicTerm &a, CType to_type) {
  std::stringstream ss;
  ss << a.getName() << "_" << a.getID();
  switch (to_type) {
  case CType::BOOL:
    return ctx.int_const(ss.str().c_str()) != 0;
    break;
  case CType::INT:
    return ctx.int_const(ss.str().c_str());
    break;
  case CType::REAL:
    return ctx.int_const(ss.str().c_str());
    break;
  case CType::BITVECTOR:
    return z3::int2bv(32, ctx.int_const(ss.str().c_str()));
    break;
  default:
    util::fatal("Unsupported type");
  }
  util::fatal("Unsupported type");
  return ctx.bool_val(false);
}
z3::expr Z3Base::convertVariableFromRealTo(const LogicTerm &a, CType to_type) {
  std::stringstream ss;
  ss << a.getName() << "_" << a.getID();
  switch (to_type) {
  case CType::BOOL:
    return ctx.real_const(ss.str().c_str()) != 0;
    break;
  case CType::INT:
    return ctx.real_const(ss.str().c_str());
    break;
  case CType::REAL:
    return ctx.real_const(ss.str().c_str());
    break;
  case CType::BITVECTOR:
    return z3::int2bv(
        32, z3::round_fpa_to_closest_integer(ctx.real_const(ss.str().c_str())));
    break;
  default:
    util::fatal("Unsupported type");
  }
  util::fatal("Unsupported type");
  return ctx.bool_val(false);
}
z3::expr Z3Base::convertVariableFromBitvectorTo(const LogicTerm &a,
                                                CType to_type) {
  std::stringstream ss;
  ss << a.getName() << "_" << a.getID();
  switch (to_type) {
  case CType::BOOL:
    return ctx.bv_const(ss.str().c_str(), 1) != 0;
    break;
  case CType::INT:
    return z3::bv2int(ctx.bv_const(ss.str().c_str(), 32), false);
    break;
  case CType::REAL:
    return z3::bv2int(ctx.bv_const(ss.str().c_str(), 32), false);
    break;
  case CType::BITVECTOR:
    return ctx.bv_const(ss.str().c_str(), a.getBitVectorSize());
    break;
  default:
    util::fatal("Unsupported type");
  }
  util::fatal("Unsupported type");
  return ctx.bool_val(false);
}

z3::expr Z3Base::convertOperator(const LogicTerm &a,
                                 z3::expr (*op)(const z3::expr &),
                                 CType to_type) {
  if (to_type == CType::ERRORTYPE)
    to_type = a.getCType();
  return op(convert(a, to_type));
}

z3::expr Z3Base::convertOperator(const LogicTerm &a, const LogicTerm &b,
                                 z3::expr (*op)(const z3::expr &,
                                                const z3::expr &),
                                 CType to_type) {
  if (to_type == CType::ERRORTYPE)
    to_type = logicutil::getTargetCType(a, b, OpType::None);
  return op(convert(a, to_type), convert(b, to_type));
}
z3::expr Z3Base::convertOperator(
    const LogicTerm &a, const LogicTerm &b, const LogicTerm &c,
    z3::expr (*op)(const z3::expr &, const z3::expr &, const z3::expr &),
    CType to_type) {
  to_type = logicutil::getTargetCType(a, b, OpType::None);
  to_type = logicutil::getTargetCType(to_type, c);
  return op(convert(a, CType::BOOL), convert(b, to_type), convert(c, to_type));
}

z3::expr Z3Base::convertOperator(std::vector<LogicTerm> terms,
                                 z3::expr (*op)(const z3::expr &,
                                                const z3::expr &),
                                 CType to_type) {
  z3::expr res = convert(static_cast<LogicTerm>(*terms.begin()), to_type);
  for (auto it = (terms.begin() + 1); it != terms.end(); ++it) {
    res = op(res, convert(static_cast<LogicTerm>(*it), to_type));
  }
  return res;
}

z3::expr Z3Base::convertConstant(const LogicTerm &a, CType to_type) {
  switch (to_type) {
  case logicbase::CType::BOOL:
    return ctx.bool_val(a.getBoolValue());
    break;
  case logicbase::CType::INT:
    return ctx.int_val(a.getIntValue());
    break;
  case logicbase::CType::REAL:
    return ctx.real_val(std::to_string(a.getFloatValue()).c_str());
    break;
  case logicbase::CType::BITVECTOR:
    return ctx.bv_val(static_cast<uint64_t>(a.getBitVectorValue()),
                      a.getBitVectorSize());
    break;
  default:
    util::fatal("Unsupported type");
  }
  util::fatal("Unsupported type");
  return ctx.bool_val(false);
}

bool Z3LogicOptimizer::makeMinimize() {
  auto it = weightedTerms.begin();
  while (it != weightedTerms.end()) {
    optimizer.add(convert(LogicTerm::neg(it->first), CType::BOOL),
                  (*it).second);
    ++it;
  }
  return false;
}
bool Z3LogicOptimizer::makeMaximize() {
  auto it = weightedTerms.begin();
  while (it != weightedTerms.end()) {
    optimizer.add(convert((*it).first, CType::BOOL), (*it).second);
    ++it;
  }
  return false;
}
bool Z3LogicOptimizer::maximize(const LogicTerm &term) {
  optimizer.maximize(convert(term, CType::REAL));
  return true;
}
bool Z3LogicOptimizer::minimize(const LogicTerm &term) {
  optimizer.minimize(convert(term, CType::REAL));
  return true;
}

void Z3LogicOptimizer::assertFormula(const LogicTerm &a) {
  if (a.getOpType() == OpType::AND) {
    for (const auto &clause : a.getNodes()) {
      clauses.insert(clause);
      if (convertWhenAssert) {
        this->optimizer.add(convert(clause, CType::BOOL));
      }
    }
  } else {
    clauses.insert(a);
    if (convertWhenAssert) {
      this->optimizer.add(convert(a, CType::BOOL));
    }
  }
}

void Z3LogicOptimizer::dumpZ3State(std::ostream &stream) {
  stream << "Z3State: " << std::endl;
  stream << optimizer << std::endl;
}

void Z3LogicOptimizer::produceInstance() {
  auto it = clauses.begin();
  while (it != clauses.end()) {
    expr c = ctx.bool_val(false);
    c = convert(*it, CType::BOOL);
    this->optimizer.add(c);
    ++it;
  }
}

Result Z3LogicOptimizer::solve() {
  z3::check_result res = this->optimizer.check();
  if (res == z3::sat) {
    this->model = new Z3Model(this->ctx, this->optimizer.get_model());
    return Result::SAT;
  }
  return Result::UNSAT;
}

void Z3LogicOptimizer::internal_reset() {
  weightedTerms.clear();
  variables.clear();
  cache.clear();
}

} // namespace z3logic