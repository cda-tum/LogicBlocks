
add_subdirectory(Logic)

add_subdirectory(App)

add_library(logicblocks::Z3Logic ALIAS Z3Logic)
add_library(logicblocks::SMTLibLogic ALIAS SMTLibLogic)
add_library(logicblocks::Logic ALIAS Logic)