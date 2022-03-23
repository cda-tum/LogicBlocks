add_library(LogicTerm_lib
            ${CMAKE_CURRENT_SOURCE_DIR}/LogicTerm/TermImpl.cpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicTerm/TermImpl.hpp

            ${CMAKE_CURRENT_SOURCE_DIR}/LogicTerm/LogicTerm.cpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicTerm/LogicTerm.hpp

            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicTerm/Logic.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/Model.hpp

            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicUtil/util_logic.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicUtil/util_logicterm.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/utils/util.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/utils/csv_util.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/utils/json_util.hpp)
target_include_directories(LogicTerm_lib PUBLIC ${PROJECT_SOURCE_DIR}/include)
target_link_libraries(LogicTerm_lib PUBLIC Boost::log Boost::log_setup)

add_library(SMTLibLogic
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/LogicBlock.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/SMTLibLogicBlock.hpp
            ${CMAKE_CURRENT_SOURCE_DIR}/LogicBlock/SMTLibLogicBlock.cpp)
target_link_libraries(SMTLibLogic PUBLIC LogicTerm_lib)
add_library(logicblocks::SMTLibLogic ALIAS SMTLibLogic)

add_library(Z3Logic
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/LogicBlock.hpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/Z3Logic.hpp
            ${CMAKE_CURRENT_SOURCE_DIR}/LogicBlock/Z3Logic.cpp
            ${${PROJECT_NAME}_SOURCE_DIR}/include/LogicBlock/Z3Model.hpp
            ${CMAKE_CURRENT_SOURCE_DIR}/LogicBlock/Z3Model.cpp)
target_link_libraries(Z3Logic PUBLIC LogicTerm_lib z3::z3lib)
add_library(logicblocks::Z3Logic ALIAS Z3Logic)

add_library(Logic INTERFACE)
target_link_libraries(Logic INTERFACE SMTLibLogic Z3Logic)
add_library(logicblocks::Logic ALIAS Logic)
