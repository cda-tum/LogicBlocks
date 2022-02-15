add_library(SMTLibLogic
                ${PROJECT_SOURCE_DIR}/src/Logic/Logic.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/Model.hpp
                
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/SMTLibLogicBlock.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/SMTLibLogicBlock.cpp
)
target_include_directories(SMTLibLogic PUBLIC
                ${PROJECT_SOURCE_DIR}/src
                ${PROJECT_SOURCE_DIR}/src/Logic/
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/
)
add_library(Z3Logic
                ${PROJECT_SOURCE_DIR}/src/Logic/Logic.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/Model.hpp
                
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Logic.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Logic.cpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Model.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Model.cpp
)
target_include_directories(Z3Logic PUBLIC
                ${PROJECT_SOURCE_DIR}/src
                ${PROJECT_SOURCE_DIR}/src/Logic/
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/
)