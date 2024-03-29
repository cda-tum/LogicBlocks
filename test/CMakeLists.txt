# macro to add a test executable for one of the project libraries
macro(PACKAGE_ADD_TEST testname linklibs)
  # create an executable in which the tests will be stored
  add_executable(${testname} ${ARGN})
  # link the Google test infrastructure and a default main function to the test executable.
  target_link_libraries(${testname} PRIVATE ${linklibs} gmock gtest_main Encodings)
  # discover tests
  gtest_discover_tests(
    ${testname}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES VS_DEBUGGER_WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
  set_target_properties(${testname} PROPERTIES FOLDER tests)
endmacro()

if(Z3_FOUND)
  package_add_test(${PROJECT_NAME}_z3Logic_test Z3Logic ${CMAKE_CURRENT_SOURCE_DIR}/test_z3.cpp
                   ${CMAKE_CURRENT_SOURCE_DIR}/test_z3_optimizer.cpp)
endif()

package_add_test(
  ${PROJECT_NAME}_utils_test Logic ${CMAKE_CURRENT_SOURCE_DIR}/test_base_bool.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/test_base_int.cpp ${CMAKE_CURRENT_SOURCE_DIR}/test_utils.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/test_smtlib.cpp)
