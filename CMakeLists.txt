cmake_minimum_required(VERSION 3.14...3.19)

#set(CMAKE_VERBOSE_MAKEFILE ON)

project(logicblocks
        LANGUAGES CXX
        VERSION 1.3.2
        DESCRIPTION "lb-core"
        )

# enable organization of targets into folders
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# configuration options
option(DEPLOY "Configure for deployment")
# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# build type settings
set(default_build_type "Release")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
	message(STATUS "Setting build type to '${default_build_type}' as none was specified.")
	set(CMAKE_BUILD_TYPE "${default_build_type}" CACHE STRING "Choose the type of build." FORCE)
	set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release" "MinSizeRel" "RelWithDebInfo")
endif()

# search for Z3
find_package(Z3)
if(Z3_FOUND AND NOT TARGET z3::z3lib)
	message(STATUS "Found Z3 with version ${Z3_VERSION_STRING}")
	add_library(z3::z3lib IMPORTED INTERFACE)
	set_property(TARGET z3::z3lib PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${Z3_CXX_INCLUDE_DIRS})
	set_property(TARGET z3::z3lib PROPERTY INTERFACE_LINK_LIBRARIES ${Z3_LIBRARIES})
	add_definitions(-DZ3_FOUND)
else()
	message(WARNING "Did not find Z3. Corresponding Method not available")
endif()

# search for Boost program_options
set(Boost_USE_MULTITHREADED ON)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package( Boost 1.70 COMPONENTS program_options log log_setup)

set(CMAKE_CXX_FLAGS "-W -Wall -Wextra -fno-limit-debug-info")
set(CMAKE_CXX_FLAGS_DEBUG "-g -O0")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

add_subdirectory(src)
