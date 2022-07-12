//
// Created by Sarah on 30.05.2022.
//
#include "LogicBlock/CNFLogicBlock.hpp"

#include "LogicUtil/util_logic.hpp"
#include "utils/logging.hpp"

namespace cnflogic {

    void CNFLogicBlock::internal_reset() {
        delete model;
        model = nullptr;
    }
    void CNFLogicBlock::produceInstance() {
        out << "" << std::endl;
    }
    Result CNFLogicBlock::solve() {
        return Result::UNSAT;
    }
    void CNFLogicBlock::dump(const LogicTerm& a, std::ostream& stream) {
        LogicBlock::dump(a, stream);
    }
    void CNFLogicBlock::dumpAll(std::ostream& stream) {
        LogicBlock::dumpAll(stream);
    }
    void CNFLogicBlock::assertFormula(const LogicTerm& a) {
        LogicTerm cnf = a;
        if (convertWhenAssert) {
            cnf = convertToCNF(a);
        }
        if (a.getOpType() == OpType::AND) {
            for (const auto& clause: cnf.getNodes()) {
                clauses.insert(clause);
            }
        } else {
            clauses.insert(cnf);
        }
    }
    void CNFLogicBlock::convert() {
        for (const auto& clause: clauses) {
            convertedClauses.insert(convert(clause));
        }
    }
    LogicTerm CNFLogicBlock::convertToCNF(const LogicTerm& a) {
        auto subnodes = a.getNodes();
        switch (a.getOpType()) {
            case OpType::Variable:
                return a;
            case OpType::Constant:
                if (a.getCType() != CType::BOOL) {
                    throw std::runtime_error("Constant is not a boolean");
                }
                if (a.getBoolValue()) {
                    return trueTerm;
                } else {
                    return falseTerm;
                }
            case OpType::NEG: {
                if (subnodes[0].getOpType() == OpType::Variable) {
                    return !subnodes[0];
                } else if (subnodes[0].getOpType() == OpType::Constant) {
                    if (subnodes[0].getCType() != CType::BOOL) {
                        throw std::runtime_error("Constant is not a boolean");
                    }
                    if (subnodes[0].getBoolValue()) {
                        return falseTerm;
                    } else {
                        return trueTerm;
                    }
                } else if (subnodes[0].getOpType() == OpType::NEG) {
                    return convertToCNF(subnodes[0].getNodes()[0]);
                } else if (subnodes[0].getOpType() == OpType::AND) {
                    LogicTerm negatedClause = LogicTerm(false);
                    for (const auto& subnode: subnodes[0].getNodes()) {
                        negatedClause = negatedClause || !subnode;
                    }
                    return convertToCNF(negatedClause);
                } else if (subnodes[0].getOpType() == OpType::OR) {
                    LogicTerm negatedClause = LogicTerm(true);
                    for (const auto& subnode: subnodes[0].getNodes()) {
                        negatedClause = negatedClause && !subnode;
                    }
                    return convertToCNF(negatedClause);
                } else {
                    throw std::runtime_error("Unsupported operation type");
                }
            }
            case OpType::AND: {
                LogicTerm convertedClause = LogicTerm(true);
                for (const auto& subnode: a.getNodes()) {
                    convertedClause = convertedClause && convertToCNF(subnode);
                }
                return convertedClause;
            }
            case OpType::OR: {
                bool allVariables = true;
                for (const auto& subnode: subnodes) {
                    if (!logicutil::isUnit(subnode) && !logicutil::isConst(subnode)) {
                        allVariables = false;
                        break;
                    }
                }
                if (allVariables) {
                    return a;
                }
                LogicTerm Z = LogicTerm(false);
                LogicTerm P = convertToCNF(subnodes[0]);
                LogicTerm Q;
                for (size_t i = 1; i < subnodes.size(); ++i) {
                    Q = convertToCNF(subnodes[i]);
                    if ((logicutil::isUnit(P)) && (logicutil::isUnit(Q))) {
                        Z = !P && !Q;
                    } else if (logicutil::isUnit(P)) {
                        LogicTerm convertedClause = LogicTerm(true);
                        for (const auto& subnode: Q.getNodes()) {
                            convertedClause = convertedClause && (P || subnode);
                        }
                        Z = convertedClause;
                    } else if (logicutil::isUnit(Q)) {
                        LogicTerm convertedClause = LogicTerm(true);
                        for (const auto& subnode: P.getNodes()) {
                            convertedClause = convertedClause && (Q || subnode);
                        }
                        Z = convertedClause;
                    } else {
                        Z = this->makeVariable("", CType::BOOL);
                        Z = convertToCNF((!Z || P)) && convertToCNF((Z || Q));
                    }
                    P = Z;
                }
                return Z;
            }
            case OpType::IMPL: {
                auto P = convertToCNF(subnodes[0]);
                auto Q = convertToCNF(subnodes[1]);
                return convertToCNF(!P || Q);
            }
            case OpType::EQ: {
                auto P = convertToCNF(subnodes[0]);
                auto Q = convertToCNF(subnodes[1]);
                return convertToCNF(convertToCNF(P && Q) || (convertToCNF(!P) && convertToCNF(!Q)));
            }
            case OpType::XOR: {
                auto P = convertToCNF(subnodes[0]);
                auto Q = convertToCNF(subnodes[1]);
                return convertToCNF((P && convertToCNF(!Q)) || (convertToCNF(!P) && Q));
            }
            default:
                throw std::runtime_error("Unsupported operation type");
        }
    }
    std::unordered_set<long long> CNFLogicBlock::convert(const LogicTerm& a) {
        switch (a.getOpType()) {
            case logicbase::OpType::Variable: {
                auto it = variables.find(a.getID());
                if (it == variables.end()) {
                    variables[a.getID()] = varId++;
                    return {variables[a.getID()]};
                } else {
                    return {it->second};
                }
            }
            case OpType::Constant: {
                if (a.getBoolValue())
                    return {1}; //True Literal
                else
                    return {2}; //False Literal
            }
            case OpType::NEG: {
                auto subnodes = a.getNodes();
                if (subnodes[0].getOpType() == OpType::Variable) {
                    auto it = variables.find(a.getNodes()[0].getID());
                    if (it == variables.end()) {
                        variables[a.getNodes()[0].getID()] = varId++;
                        return {-variables[a.getNodes()[0].getID()]};
                    } else {
                        return {-it->second};
                    }
                } else if (subnodes[0].getOpType() == OpType::Constant) {
                    if (subnodes[0].getBoolValue())
                        return {-1}; //True Literal
                    else
                        return {-2}; //False Literal
                } else if (subnodes[0].getOpType() == OpType::NEG) {
                    return convert(subnodes[0].getNodes()[0]);
                } else if (subnodes[0].getOpType() == OpType::AND) {
                    LogicTerm negatedClause = LogicTerm(true);
                    for (const auto& subnode: subnodes[0].getNodes()) {
                        negatedClause = negatedClause || !subnode;
                    }
                    return convert(negatedClause);
                } else if (subnodes[0].getOpType() == OpType::OR) {
                    LogicTerm negatedClause = LogicTerm(false);
                    for (const auto& subnode: subnodes[0].getNodes()) {
                        negatedClause = negatedClause && !subnode;
                    }
                    return convert(negatedClause);
                } else {
                    throw std::runtime_error("Unsupported operation type");
                }
            }
            case OpType::OR: {
                std::unordered_set<long long> convertedClause;
                for (const auto& subnode: a.getNodes()) {
                    convertedClause.insert(convert(subnode).begin(), convert(subnode).end());
                }
                return convertedClause;
            }
            default:
                throw std::runtime_error("Unsupported operation type");
        }
        return {};
    }

} // namespace cnflogic