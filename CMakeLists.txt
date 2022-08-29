cmake_minimum_required(VERSION 3.14...3.19)

#set(CMAKE_VERBOSE_MAKEFILE ON)

project(logicblocks
        LANGUAGES CXX
        VERSION 1.3.5
        DESCRIPTION "lb-core"
        )

# enable organization of targets into folders
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

# configuration options
option(DEPLOY "Configure for deployment")
option(COVERAGE "Configure for coverage report generation")
option(GENERATE_POSITION_INDEPENDENT_CODE "Generate position independent code")
option(BUILD_LB_TESTS "Also build tests for LogicBlocks project")


if (DEFINED ENV{DEPLOY})
    set(DEPLOY $ENV{DEPLOY} CACHE BOOL "Use deployment configuration from environment" FORCE)
    message(STATUS "Setting deployment configuration to '${DEPLOY}' from environment")
endif ()

# set deployment specific options
if (DEPLOY)
    # set the macOS deployment target appropriately
    set(CMAKE_OSX_DEPLOYMENT_TARGET "10.15" CACHE STRING "" FORCE)
endif ()

macro(check_submodule_present MODULENAME)
    if (NOT EXISTS "${PROJECT_SOURCE_DIR}/extern/${MODULENAME}/CMakeLists.txt")
        message(FATAL_ERROR "${MODULENAME} submodule not cloned properly. Please run `git submodule update --init --recursive` from the main project directory")
    endif ()
endmacro()

# build type settings
set(default_build_type "Release")
if (NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    message(STATUS "Setting build type to '${default_build_type}' as none was specified.")
    set(CMAKE_BUILD_TYPE "${default_build_type}" CACHE STRING "Choose the type of build." FORCE)
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release" "MinSizeRel" "RelWithDebInfo")
endif ()

check_submodule_present(plog)

# Add path for custom modules
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# search for Z3
find_package(Z3 4.8.15.0)
if (Z3_FOUND AND NOT TARGET z3::z3lib)
    message(STATUS "Found Z3 with version ${Z3_VERSION_STRING}")
    add_library(z3::z3lib IMPORTED INTERFACE)
    set_property(TARGET z3::z3lib PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${Z3_CXX_INCLUDE_DIRS})
    set_property(TARGET z3::z3lib PROPERTY INTERFACE_LINK_LIBRARIES ${Z3_LIBRARIES})
    add_compile_definitions(Z3_FOUND)
endif ()

add_subdirectory(src)

add_subdirectory(app)

set(BUILD_LB_TESTS ON)
# add test code
if (BUILD_LB_TESTS)
    enable_testing()
    include(GoogleTest)
    add_subdirectory(test)
endif ()