cmake_minimum_required (VERSION 3.18)
project (KLEEBMC)

set (KLEEBMC_VERSION_MAJOR 0)
set (KLEEBMC_VERSION_MINOR 1)
set (KLEEBMC_VERSION_PATCH 0)
set (KLEEBMC_VERSION "${ESBMC_VERSION_MAJOR}.${ESBMC_VERSION_MINOR}.${ESBMC_VERSION_PATCH}")

set(INSTALL_BIN_DIR ${CMAKE_INSTALL_PREFIX} CACHE PATH "Installation directory for executables")
set(INSTALL_INC_DIR include CACHE PATH "Installation directory for headers")
set(INSTALL_DATA_DIR ${CMAKE_INSTALL_PREFIX} CACHE PATH "Installation directory for data files")

# --------------------------------------------------
# LLVM
# --------------------------------------------------
find_package(LLVM 14 REQUIRED CONFIG)
list(APPEND CMAKE_MODULE_PATH "${LLVM_DIR}")
include(AddLLVM)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "LLVM include dir: ${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM libraries dir: ${LLVM_LIBRARY_DIRS}")

option(LLVM_LINK_DYLIB "Link with LLVM dynamically" ON)

if(LLVM_LINK_DYLIB)
	message(STATUS "LLVM linking: dynamic")
	set(LLVM_LIBS LLVM)
else()
	message(STATUS "LLVM linking: static")

	# Find the libraries that correspond to the LLVM components
	# that we wish to use
	llvm_map_components_to_libnames(LLVM_LIBS bitwriter core irreader
		linker support)
endif()

include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

include_directories(include)
add_subdirectory(lib)
add_subdirectory(transforms)

# Copy run scripts
configure_file(${CMAKE_SOURCE_DIR}/scripts/klee-bmc ${CMAKE_BINARY_DIR}/bin/klee-bmc COPYONLY)
configure_file(${CMAKE_SOURCE_DIR}/scripts/ktest_parser.py ${CMAKE_BINARY_DIR}/bin/ktest_parser.py COPYONLY)
configure_file(${CMAKE_SOURCE_DIR}/scripts/ktest_parser.py ${CMAKE_BINARY_DIR}/bin/acsl_rewriter.py COPYONLY)

install(PROGRAMS scripts/klee-bmc DESTINATION ${CMAKE_INSTALL_BINDIR})
install(PROGRAMS scripts/ktest_parser.py DESTINATION ${CMAKE_INSTALL_BINDIR})
install(PROGRAMS scripts/acsl_rewriter.py DESTINATION ${CMAKE_INSTALL_BINDIR})

# --------------------------------------------------
# Lit
# --------------------------------------------------
find_program(LIT_TOOL lit)
option(ENABLE_TESTS "Enable testing" ON)

if(ENABLE_TESTS AND NOT LIT_TOOL)
  message(WARNING "Could not find lit tool. Tests will not be built.")
  set(ENABLE_TESTS OFF)
endif()

find_program(FILECHECK_TOOL FileCheck HINTS ${LLVM_TOOLS_BINARY_DIR})
if(ENABLE_TESTS AND NOT FILECHECK_TOOL)
  message(WARNING "Could not find FileCheck tool. Tests will not be built.")
  set(ENABLE_TESTS OFF)
endif()

if(ENABLE_TESTS)
  add_subdirectory(test)
endif()
