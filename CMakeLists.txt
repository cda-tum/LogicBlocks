# set required cmake version
cmake_minimum_required(VERSION 3.19...3.28)

project(
  logicblocks
  LANGUAGES CXX
  VERSION 1.3.5
  DESCRIPTION "lb-core")

configure_file("${${PROJECT_NAME}_SOURCE_DIR}/cmake/version.hpp.in"
               "${${PROJECT_NAME}_SOURCE_DIR}/include/version.hpp")

# enable organization of targets into folders
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

# Set a default build type if none was specified
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  message(STATUS "Setting build type to 'Release' as none was specified.")
  set(CMAKE_BUILD_TYPE
      Release
      CACHE STRING "Choose the type of build." FORCE)
  # Set the possible values of build type for cmake-gui, ccmake
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release" "MinSizeRel"
                                               "RelWithDebInfo")
endif()

# Require C++ standard
set_property(GLOBAL PROPERTY CMAKE_CXX_STANDARD_REQUIRED ON)
set_property(GLOBAL PROPERTY CXX_EXTENSIONS OFF)

# configuration options
option(ENABLE_COVERAGE "Configure for coverage report generation")
option(GENERATE_POSITION_INDEPENDENT_CODE "Generate position independent code" ON)

# Generate compile_commands.json to make it easier to work with clang based tools
set(CMAKE_EXPORT_COMPILE_COMMANDS
    ON
    CACHE BOOL "Export compile commands" FORCE)

option(DEPLOY "Configure for deployment")
if(DEFINED ENV{DEPLOY})
  set(DEPLOY
      $ENV{DEPLOY}
      CACHE BOOL "Use deployment configuration from environment" FORCE)
  message(STATUS "Setting deployment configuration to '${DEPLOY}' from environment")
elseif(DEFINED ENV{CI})
  set(DEPLOY
      ON
      CACHE BOOL "Set deployment configuration to ON for CI" FORCE)
  message(STATUS "Setting deployment configuration to '${DEPLOY}' for CI")
endif()

# set deployment specific options
if(DEPLOY)
  # set the macOS deployment target appropriately
  set(CMAKE_OSX_DEPLOYMENT_TARGET
      "10.15"
      CACHE STRING "" FORCE)
endif()

# Add path for custom modules
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

option(BUILD_LB_TESTS "Also build tests for LogicBlocks project" ON)

include(cmake/ExternalDependencies.cmake)

add_subdirectory(src)

# add test code
if(BUILD_LB_TESTS)
  enable_testing()
  include(GoogleTest)
  add_subdirectory(test)
endif()
