
add_library(LogicTerm_lib 
                    ${PROJECT_SOURCE_DIR}/src/Logic/Logic.hpp
                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicTerm/TermImpl.hpp
                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicTerm/TermImpl.cpp
                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicTerm/LogicTerm.hpp 
                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicTerm/LogicTerm.cpp 
                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicUtil/util_logic.h
                    )
                    
target_include_directories(LogicTerm_lib PUBLIC 
                                    ${PROJECT_SOURCE_DIR}/src 
                                    ${PROJECT_SOURCE_DIR}/utils 
                                    ${PROJECT_SOURCE_DIR}/src/Logic
                                    ${PROJECT_SOURCE_DIR}/src/Logic/LogicUtil)