cmake_minimum_required(VERSION 3.5 FATAL_ERROR)

project(minisat)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(BUILD_BINARIES  "Build the solver binary" ON)
option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE   "Use SORELEASE in shared library filename." ON)
option(QUIET           "Disable all output to stdout" OFF)

#--------------------------------------------------------------------------------------------------
# Library version:

set(MINISAT_SOMAJOR   2)
set(MINISAT_SOMINOR   2)
set(MINISAT_SORELEASE 0)

# Compute VERSION and SOVERSION:
if (USE_SORELEASE)
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR}.${MINISAT_SORELEASE})
else()
  set(MINISAT_VERSION ${MINISAT_SOMAJOR}.${MINISAT_SOMINOR})
endif()
set(MINISAT_SOVERSION ${MINISAT_SOMAJOR})

#--------------------------------------------------------------------------------------------------
# Dependencies:

if(BUILD_BINARIES)
  find_package(ZLIB)
  include_directories(${ZLIB_INCLUDE_DIR})
endif()
include_directories(${minisat_SOURCE_DIR})

#--------------------------------------------------------------------------------------------------
# Compile flags:

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)
set(CMAKE_CXX_STANDARD 11)
if(QUIET)
  add_compile_definitions("QUIET")
endif()

#--------------------------------------------------------------------------------------------------
# Build Targets:

set(MINISAT_LIB_SOURCES
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/simp/SimpSolver.cc
    minisat/cminisat.cc)

add_library(minisat-lib-static STATIC ${MINISAT_LIB_SOURCES})
add_library(minisat-lib-shared SHARED ${MINISAT_LIB_SOURCES})

if(BUILD_BINARIES)
  add_executable(minisat_core minisat/core/Main.cc)
  add_executable(minisat_simp minisat/simp/Main.cc)

  target_link_libraries(minisat_core ${ZLIB_LIBRARY})
  target_link_libraries(minisat_simp ${ZLIB_LIBRARY})

  if(STATIC_BINARIES)
    target_link_libraries(minisat_core minisat-lib-static)
    target_link_libraries(minisat_simp minisat-lib-static)
  else()
    target_link_libraries(minisat_core minisat-lib-shared)
    target_link_libraries(minisat_simp minisat-lib-shared)
  endif()
endif()

set_target_properties(minisat-lib-static PROPERTIES OUTPUT_NAME "minisat")
set_target_properties(minisat-lib-shared
  PROPERTIES
    OUTPUT_NAME "minisat"
    VERSION ${MINISAT_VERSION}
    SOVERSION ${MINISAT_SOVERSION})

if(BUILD_BINARIES)
  set_target_properties(minisat_simp       PROPERTIES OUTPUT_NAME "minisat")
endif()

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS minisat-lib-static minisat-lib-shared
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

if(BUILD_BINARIES)
  install(TARGETS minisat_core minisat_simp
          RUNTIME DESTINATION bin)
endif()

install(DIRECTORY minisat/mtl minisat/utils minisat/core minisat/simp
        DESTINATION include/minisat
        FILES_MATCHING PATTERN "*.h")
