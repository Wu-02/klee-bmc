# Find all .c files in the LIBS directory
file(GLOB_RECURSE C_FILES "**/*.c")

set(INCLUDE_DIR "${LLVM_LIBRARY_DIRS}/clang/${LLVM_PACKAGE_VERSION}/include/")

# Create targets for 64-bit and 32-bit versions
foreach(ARCH 64 32)
	set(TARGET_NAME "bitcode${ARCH}")
	add_custom_target(${TARGET_NAME} ALL)

	foreach(C_FILE ${C_FILES})
		# Get the output file name
		get_filename_component(NAME ${C_FILE} NAME_WE)
		file(RELATIVE_PATH REL_PATH ${CMAKE_CURRENT_SOURCE_DIR} ${C_FILE})
		get_filename_component(REL_DIR ${REL_PATH} DIRECTORY)
		string(REPLACE "/" "_" TARGET_SUFFIX ${REL_DIR})
		string(REPLACE ".c" ".bc" OUT_FILE ${REL_PATH})

		if(ARCH EQUAL 32)
			set(ARCH_FLAG "-m32")
			set(OUT_DIR "${CMAKE_INSTALL_LIBDIR}32")
		else()
			set(ARCH_FLAG "")
			set(OUT_DIR "${CMAKE_INSTALL_LIBDIR}")
		endif()

		add_custom_command(
			OUTPUT "${OUT_DIR}/${OUT_FILE}"
			COMMAND ${CMAKE_COMMAND} "-E" "make_directory" "${OUT_DIR}/${REL_DIR}"
			COMMAND ${CMAKE_C_COMPILER} "-I${INCLUDE_DIR}" "-I${CMAKE_SOURCE_DIR}/include" "-O3" "-emit-llvm" "-c" "${C_FILE}" "${ARCH_FLAG}" "-o" "${OUT_DIR}/${OUT_FILE}"
			DEPENDS ${C_FILE}
			COMMENT "Compiling ${C_FILE} to ${OUT_DIR}/${OUT_FILE}"
		)

		target_sources(${TARGET_NAME} PRIVATE "${OUT_DIR}/${OUT_FILE}")
	endforeach()
endforeach()
