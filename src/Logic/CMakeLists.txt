add_subdirectory(LogicTerm)
add_subdirectory(LogicBlock)

target_link_libraries(SMTLibLogic PUBLIC
                    LogicTerm_lib
                    Boost::log
                    Boost::log_setup
)
target_link_libraries(Z3Logic PUBLIC
                    LogicTerm_lib
                    Boost::log
                    Boost::log_setup
                    z3::z3lib
)

add_library(Logic 
                ${PROJECT_SOURCE_DIR}/src/Logic/Logic.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/Model.hpp
                
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/SMTLibLogicBlock.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/SMTLibLogicBlock.cpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Logic.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Logic.cpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Model.hpp
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/Z3Model.cpp
    )
target_include_directories(Logic PUBLIC
                ${PROJECT_SOURCE_DIR}/src
                ${PROJECT_SOURCE_DIR}/src/Logic/
                ${PROJECT_SOURCE_DIR}/src/Logic/LogicBlock/
)
target_link_libraries(Logic PUBLIC
                LogicTerm_lib
                Boost::log
                Boost::log_setup
                z3::z3lib
                )