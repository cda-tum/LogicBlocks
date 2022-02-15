add_executable(${PROJECT_NAME}_app ${CMAKE_CURRENT_SOURCE_DIR}/app.cpp)
target_link_libraries(${PROJECT_NAME}_app PUBLIC 
                    LogicTerm_lib
                    Boost::program_options
                    Boost::log
                    Boost::log_setup)

target_include_directories(${PROJECT_NAME}_app PUBLIC
						${PROJECT_SOURCE_DIR}/src
                        ${PROJECT_SOURCE_DIR}/src/Logic)