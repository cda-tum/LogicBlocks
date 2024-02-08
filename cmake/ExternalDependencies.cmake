# Declare all external dependencies and make sure that they are available.

include(FetchContent)
set(FETCH_PACKAGES "")

# search for Z3
find_package(Z3 4.8.15)
if(NOT Z3_FOUND)
  message(WARNING "Did not find Z3. Some targets will not be available")
endif()

set(PLOG_VERSION
    1.1.10
    CACHE STRING "Plog version")
set(PLOG_URL https://github.com/SergiusTheBest/plog/archive/refs/tags/${PLOG_VERSION}.tar.gz)
if(CMAKE_VERSION VERSION_GREATER_EQUAL 3.24)
  FetchContent_Declare(plog URL ${PLOG_URL} FIND_PACKAGE_ARGS ${PLOG_VERSION})
  list(APPEND FETCH_PACKAGES plog)
else()
  find_package(plog ${PLOG_VERSION} QUIET)
  if(NOT plog_FOUND)
    FetchContent_Declare(plog URL ${PLOG_URL})
    list(APPEND FETCH_PACKAGES plog)
  endif()
endif()

if(BUILD_LB_TESTS)
  set(gtest_force_shared_crt
      ON
      CACHE BOOL "" FORCE)
  set(GTEST_VERSION
      1.14.0
      CACHE STRING "Google Test version")
  set(GTEST_URL https://github.com/google/googletest/archive/refs/tags/v${GTEST_VERSION}.tar.gz)
  if(CMAKE_VERSION VERSION_GREATER_EQUAL 3.24)
    FetchContent_Declare(googletest URL ${GTEST_URL} FIND_PACKAGE_ARGS ${GTEST_VERSION} NAMES GTest)
    list(APPEND FETCH_PACKAGES googletest)
  else()
    find_package(googletest ${GTEST_VERSION} QUIET NAMES GTest)
    if(NOT googletest_FOUND)
      FetchContent_Declare(googletest URL ${GTEST_URL})
      list(APPEND FETCH_PACKAGES googletest)
    endif()
  endif()
endif()

# Make all declared dependencies available.
FetchContent_MakeAvailable(${FETCH_PACKAGES})

set_target_properties(plog PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES
                                      $<TARGET_PROPERTY:plog,INTERFACE_INCLUDE_DIRECTORIES>)
