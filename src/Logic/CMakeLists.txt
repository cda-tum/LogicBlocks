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