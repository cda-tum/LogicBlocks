cmake_minimum_required(VERSION 3.14...3.19)

#set(CMAKE_VERBOSE_MAKEFILE ON)

project(logicblocks
        LANGUAGES CXX
        VERSION 1.3.3
        DESCRIPTION "lb-core"
        )

# enable organization of targets into folders
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

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
endif()

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/plog" "extern/plog")


add_subdirectory(src)

add_subdirectory(app)
