set(KLEEBMC_BIN "${CMAKE_INSTALL_PREFIX}/bin/klee-bmc")
set(TESTING_TOOL "${CMAKE_CURRENT_SOURCE_DIR}/testing_tool.py")

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/lit.site.cfg.in
  ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
  @ONLY
)

add_custom_target(tests
  COMMAND ${LIT_TOOL} ${CMAKE_CURRENT_BINARY_DIR}
  COMMENT "Running tests"
  USES_TERMINAL
)