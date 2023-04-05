#ifndef UTIL_LOGICBLOCK_H
#define UTIL_LOGICBLOCK_H

#include "LogicBlock/LogicBlock.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"
#include "LogicBlock/Z3Logic.hpp"
#include "LogicTerm/Logic.hpp"

#ifdef Z3_FOUND
    #include <z3++.h>
    #include <z3_api.h>
#endif

namespace logicutil {
    using namespace logicbase;

    enum class ParamType {
        STR,
        BOOL,
        DOUBLE,
        UINT,
    };

    class Param {
    public:
        ParamType   type;
        std::string name;
        std::string strvalue;
        bool        bvalue  = false;
        double      dvalue  = 0.;
        uint32_t    uivalue = 0;
        Param(std::string n, std::string value):
            type(ParamType::STR), name(std::move(n)), strvalue(std::move(value)) {}

        Param(std::string n, bool value):
            type(ParamType::BOOL), name(std::move(n)), bvalue(value) {}

        Param(std::string n, double value):
            type(ParamType::DOUBLE), name(std::move(n)), dvalue(value) {}

        Param(std::string n, uint32_t value):
            type(ParamType::UINT), name(std::move(n)), uivalue(value) {}
    };
    class Params {
        std::vector<Param> params;

    public:
        void addParam(const std::string& n, const std::string& value) {
            params.emplace_back(n, value);
        }
        void addParam(const std::string& n, bool value) {
            params.emplace_back(n, value);
        }
        void addParam(const std::string& n, double value) {
            params.emplace_back(n, value);
        }
        void addParam(const std::string& n, uint32_t value) {
            params.emplace_back(n, value);
        }
        [[nodiscard]] std::vector<Param> getParams() const {
            return params;
        }
    };

    inline void setZ3Params(z3::params& p, const Params& params) {
        for (const auto& param: params.getParams()) {
            switch (param.type) {
                case ParamType::STR:
                    p.set(param.name.c_str(), param.strvalue.c_str());
                    break;
                case ParamType::BOOL:
                    p.set(param.name.c_str(), param.bvalue);
                    break;
                case ParamType::DOUBLE:
                    p.set(param.name.c_str(), param.dvalue);
                    break;
                case ParamType::UINT:
                    p.set(param.name.c_str(), param.uivalue);
                    break;
                default:
                    break;
            }
        }
    }

    inline bool isZ3Available() {
#ifdef Z3_FOUND
        return true;
#else
        return false;
#endif
    }

    inline std::unique_ptr<LogicBlock> getZ3LogicBlock(bool& success, bool convertWhenAssert, const Params& params = Params()) {
#ifdef Z3_FOUND
        auto       c   = std::make_shared<z3::context>();
        auto       slv = std::make_shared<z3::solver>(*c);
        z3::params p(*c);
        setZ3Params(p, params);
        slv->set(p);
        success = true;
        return std::make_unique<z3logic::Z3LogicBlock>(c, slv, convertWhenAssert);
#else
        success = false;
        return nullptr;
            //throw std::runtime_error("Z3 not found");
#endif
    }

    inline std::unique_ptr<LogicBlockOptimizer> getZ3LogicOptimizer(bool& success, bool convertWhenAssert, const Params& params = Params()) {
#ifdef Z3_FOUND
        auto       c   = std::make_shared<z3::context>();
        auto       opt = std::make_shared<z3::optimize>(*c);
        z3::params p(*c);
        setZ3Params(p, params);
        opt->set(p);
        success = true;
        return std::make_unique<z3logic::Z3LogicOptimizer>(c, opt, convertWhenAssert);
#else
        success = false;
        return nullptr;
            //throw std::runtime_error("Z3 not found");
#endif
    }

} // namespace logicutil

#endif //UTIL_LOGICBLOCK_H
