#include "LogicBlock/Z3Logic.hpp"

#include "LogicBlock/Z3Model.hpp"
#include "LogicUtil/util_logic.hpp"
#include "utils/logging.hpp"

#include <iostream>

namespace z3logic {

    z3::expr Z3Base::getExprTerm(const uint64_t id, const CType type, Z3Base* z3base) {
        if (z3base->variables.find(id) == z3base->variables.end() ||
            !z3base->variables.at(id)[static_cast<int>(type)].first) {
            util::fatal("Variable not found");
        }
        return z3base->variables.at(id)[static_cast<int>(type)].second;
    }

    z3::expr Z3Base::convert(const LogicTerm& a, CType toType) {
        if (a.getOpType() == OpType::Constant) {
            return convertConstant(a, toType);
        }
        std::vector<std::pair<bool, z3::expr>> v;
        if (cache.find(a) != cache.end()) {
            v = cache.at(a);
            if (v[static_cast<int>(toType)].first) {
                return v[static_cast<int>(toType)].second;
            }
        } else {
            for (int32_t i = 0; i < 4; i++) {
                v.emplace_back(false, ctx.bool_val(false));
            }
        }
        switch (a.getOpType()) {
            case OpType::Variable: {
                v[static_cast<int>(toType)].first  = true;
                v[static_cast<int>(toType)].second = convertVariableTo(a, toType);
            } break;

            case OpType::AND: {
                z3::expr s         = this->ctx.bool_val(true);
                bool     alternate = false;
                for (const LogicTerm& lt: a.getNodes()) {
                    if (alternate) {
                        s = s && convert(lt, toType);
                    } else {
                        s = convert(lt, toType) && s;
                    }
                    alternate = !alternate;
                }
                v[static_cast<int>(toType)].second = s.simplify();
                v[static_cast<int>(toType)].first  = true;
            } break;
            case OpType::OR: {
                z3::expr s         = this->ctx.bool_val(false);
                bool     alternate = false;
                for (const LogicTerm& lt: a.getNodes()) {
                    if (alternate) {
                        s = s || convert(lt, toType);
                    } else {
                        s = convert(lt, toType) || s;
                    }
                    alternate = !alternate;
                }
                v[static_cast<int>(toType)].second = s.simplify();
                v[static_cast<int>(toType)].first  = true;
            } break;
            case OpType::EQ:
                v[static_cast<int>(toType)].second = convertOperator(
                        a.getNodes()[0], a.getNodes()[1], z3::operator==, CType::ERRORTYPE);
                v[static_cast<int>(toType)].first = true;
                break;
            case OpType::XOR:
                v[static_cast<int>(toType)].second = convertOperator(
                        a.getNodes()[0], a.getNodes()[1], z3::operator!=, CType::ERRORTYPE);
                v[static_cast<int>(toType)].first = true;
                break;
            case OpType::NEG:
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], z3::operator!, CType::ERRORTYPE);
                v[static_cast<int>(toType)].first = true;
                break;
            case OpType::ITE:
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], a.getNodes()[2],
                                        z3::ite, CType::ERRORTYPE);
                v[static_cast<int>(toType)].first = true;
                break;
            case OpType::IMPL:
                v[static_cast<int>(toType)].second = convertOperator(
                        a.getNodes()[0], a.getNodes()[1], z3::implies, CType::BOOL);
                v[static_cast<int>(toType)].first = true;
                break;
            case OpType::ADD: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator+,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::SUB: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator-,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::MUL: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator*,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::DIV: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator/,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::GT: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator>,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::LT: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator<,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::GTE: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator>=,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::LTE: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator<=,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::BitAnd: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator&, logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::BitOr: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator|,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::BitXor: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes(), z3::operator^,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            case OpType::BitEq: {
                v[static_cast<int>(toType)].second =
                        convertOperator(a.getNodes()[0], a.getNodes()[1], z3::operator==,
                                        logicutil::extractNumberType(a.getNodes()));
                v[static_cast<int>(toType)].first = true;
            } break;
            default:
                util::fatal("Unsupported operation");
                break;
        }
        cache.insert_or_assign(a, v);
        return cache.at(a)[static_cast<int>(toType)].second;
    }

    void Z3LogicBlock::assertFormula(const LogicTerm& a) {
        if (a.getOpType() == OpType::AND) {
            for (const auto& clause: a.getNodes()) {
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

    void Z3LogicBlock::dumpZ3State(std::ostream& stream) {
        stream << "Z3State: " << std::endl;
        stream << solver << std::endl;
    }

    void Z3LogicBlock::produceInstance() {
        for (const auto& clause: clauses) {
            solver.add(convert(clause, CType::BOOL));
        }
    }

    Result Z3LogicBlock::solve() {
        produceInstance();
        const auto res = solver.check();
        if (res == z3::sat) {
            model = new Z3Model(ctx, solver.get_model());
            return Result::SAT;
        }
        return Result::UNSAT;
    }

    void Z3LogicBlock::internalReset() {
        variables.clear();
        cache.clear();
        solver.reset();
        Z3Base::variables.clear();
    }

    z3::expr Z3Base::convertVariableTo(const LogicTerm& a, CType toType) {
        std::vector<std::pair<bool, z3::expr>> v;
        if (variables.find(a.getID()) != variables.end()) {
            v = variables.at(a.getID());
            if (v[static_cast<int>(toType)].first) {
                return v[static_cast<int>(toType)].second;
            }
        } else {
            for (int32_t i = 0; i < 4; i++) {
                v.emplace_back(false, ctx.bool_val(false));
            }
        }
        v[static_cast<int>(toType)].first = true;
        switch (a.getCType()) {
            case CType::BOOL:
                v[static_cast<int>(toType)].second = convertVariableFromBoolTo(a, toType);
                break;
            case CType::INT:
                v[static_cast<int>(toType)].second = convertVariableFromIntTo(a, toType);
                break;
            case CType::REAL:
                v[static_cast<int>(toType)].second = convertVariableFromRealTo(a, toType);
                break;
            case CType::BITVECTOR:
                v[static_cast<int>(toType)].second =
                        convertVariableFromBitvectorTo(a, toType);
                break;
            default:
                util::fatal("Unsupported type");
                break;
        }
        variables.insert_or_assign(a.getID(), v);
        return v[static_cast<int>(toType)].second;
    }
    z3::expr Z3Base::convertVariableFromBoolTo(const LogicTerm& a, CType toType) {
        std::stringstream ss;
        ss << a.getName() << "_" << a.getID();
        switch (toType) {
            case CType::BOOL:
                return ctx.bool_const(ss.str().c_str());
            case CType::INT:
                return z3::ite(ctx.bool_const(ss.str().c_str()), ctx.int_val(1),
                               ctx.int_val(0));
            case CType::REAL:
                return z3::ite(ctx.bool_const(ss.str().c_str()), ctx.real_val(1),
                               ctx.real_val(0));
            case CType::BITVECTOR:
                return ite(ctx.bool_const(ss.str().c_str()), ctx.bv_val(1, 32),
                           ctx.bv_val(0, 32));
            default:
                util::fatal("Unsupported type");
        }
        util::fatal("Unsupported type");
        return ctx.bool_val(false);
    }
    z3::expr Z3Base::convertVariableFromIntTo(const LogicTerm& a, CType toType) {
        std::stringstream ss;
        ss << a.getName() << "_" << a.getID();
        switch (toType) {
            case CType::BOOL:
                return ctx.int_const(ss.str().c_str()) != 0;
            case CType::INT:
            case CType::REAL:
                return ctx.int_const(ss.str().c_str());
            case CType::BITVECTOR:
                return z3::int2bv(32U, ctx.int_const(ss.str().c_str()));
            default:
                util::fatal("Unsupported type");
        }
        util::fatal("Unsupported type");
        return ctx.bool_val(false);
    }
    z3::expr Z3Base::convertVariableFromRealTo(const LogicTerm& a, CType toType) {
        std::stringstream ss;
        ss << a.getName() << "_" << a.getID();
        switch (toType) {
            case CType::BOOL:
                return ctx.real_const(ss.str().c_str()) != 0;
            case CType::INT:
            case CType::REAL:
                return ctx.real_const(ss.str().c_str());
            case CType::BITVECTOR:
                return z3::int2bv(32U, z3::round_fpa_to_closest_integer(ctx.real_const(ss.str().c_str())));
            default:
                util::fatal("Unsupported type");
        }
        util::fatal("Unsupported type");
        return ctx.bool_val(false);
    }
    z3::expr Z3Base::convertVariableFromBitvectorTo(const LogicTerm& a,
                                                    CType            toType) {
        std::stringstream ss;
        ss << a.getName() << "_" << a.getID();
        switch (toType) {
            case CType::BOOL:
                return ctx.bv_const(ss.str().c_str(), 32U) != 0;
            case CType::INT:
            case CType::REAL:
                return z3::bv2int(ctx.bv_const(ss.str().c_str(), 32U), false);
            case CType::BITVECTOR:
                return ctx.bv_const(ss.str().c_str(), a.getBitVectorSize());
            default:
                util::fatal("Unsupported type");
        }
        util::fatal("Unsupported type");
        return ctx.bool_val(false);
    }

    z3::expr Z3Base::convertOperator(const LogicTerm& a,
                                     z3::expr (*op)(const z3::expr&),
                                     CType toType) {
        if (toType == CType::ERRORTYPE) {
            toType = a.getCType();
        }
        return op(convert(a, toType));
    }

    z3::expr Z3Base::convertOperator(const LogicTerm& a, const LogicTerm& b,
                                     z3::expr (*op)(const z3::expr&,
                                                    const z3::expr&),
                                     CType toType) {
        if (toType == CType::ERRORTYPE) {
            toType = logicutil::getTargetCType(a, b, OpType::None);
        }
        return op(convert(a, toType), convert(b, toType));
    }
    z3::expr Z3Base::convertOperator(
            const LogicTerm& a, const LogicTerm& b, const LogicTerm& c,
            z3::expr (*op)(const z3::expr&, const z3::expr&, const z3::expr&),
            CType toType) {
        toType = logicutil::getTargetCType(a, b, OpType::None);
        toType = logicutil::getTargetCType(toType, c);
        return op(convert(a, CType::BOOL), convert(b, toType), convert(c, toType));
    }

    z3::expr Z3Base::convertOperator(const std::vector<LogicTerm>& terms,
                                     z3::expr (*op)(const z3::expr&,
                                                    const z3::expr&),
                                     CType toType) {
        z3::expr res = convert(static_cast<LogicTerm>(*terms.begin()), toType);
        for (auto it = (terms.begin() + 1); it != terms.end(); ++it) {
            res = op(res, convert(static_cast<LogicTerm>(*it), toType));
        }
        return res;
    }

    z3::expr Z3Base::convertConstant(const LogicTerm& a, CType toType) {
        switch (toType) {
            case logicbase::CType::BOOL:
                return ctx.bool_val(a.getBoolValue());
            case logicbase::CType::INT:
                return ctx.int_val(a.getIntValue());
            case logicbase::CType::REAL:
                return ctx.real_val(std::to_string(a.getFloatValue()).c_str());
            case logicbase::CType::BITVECTOR:
                return ctx.bv_val(static_cast<uint64_t>(a.getBitVectorValue()), a.getBitVectorSize());
            default:
                util::fatal("Unsupported type");
        }
        util::fatal("Unsupported type");
        return ctx.bool_val(false);
    }

    bool Z3LogicOptimizer::makeMinimize() {
        for (const auto& [term, weight]: weightedTerms) {
            optimizer.add(convert(LogicTerm::neg(term), CType::BOOL), static_cast<unsigned>(weight));
        }
        return false;
    }

    bool Z3LogicOptimizer::makeMaximize() {
        for (const auto& [term, weight]: weightedTerms) {
            optimizer.add(convert(term, CType::BOOL), static_cast<unsigned>(weight));
        }
        return false;
    }

    bool Z3LogicOptimizer::maximize(const LogicTerm& term) {
        optimizer.maximize(convert(term, CType::REAL));
        return true;
    }
    bool Z3LogicOptimizer::minimize(const LogicTerm& term) {
        optimizer.minimize(convert(term, CType::REAL));
        return true;
    }

    void Z3LogicOptimizer::assertFormula(const LogicTerm& a) {
        if (a.getOpType() == OpType::AND) {
            for (const auto& clause: a.getNodes()) {
                clauses.insert(clause);
                if (convertWhenAssert) {
                    optimizer.add(convert(clause, CType::BOOL));
                }
            }
        } else {
            clauses.insert(a);
            if (convertWhenAssert) {
                optimizer.add(convert(a, CType::BOOL));
            }
        }
    }

    void Z3LogicOptimizer::dumpZ3State(std::ostream& stream) {
        stream << "Z3State: " << std::endl;
        stream << optimizer << std::endl;
    }

    void Z3LogicOptimizer::produceInstance() {
        for (const auto& clause: clauses) {
            optimizer.add(convert(clause, CType::BOOL));
        }
    }

    Result Z3LogicOptimizer::solve() {
        produceInstance();
        const auto res = optimizer.check();
        if (res == z3::sat) {
            model = new Z3Model(ctx, optimizer.get_model());
            return Result::SAT;
        }
        return Result::UNSAT;
    }

    void Z3LogicOptimizer::internalReset() {
        weightedTerms.clear();
        variables.clear();
        cache.clear();
        Z3Base::variables.clear();
        optimizer = z3::optimize{ctx};
    }

} // namespace z3logic
