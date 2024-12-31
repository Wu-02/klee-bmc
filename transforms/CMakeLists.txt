include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")

add_library(KleeBMCPasses MODULE
                           "AInliner.cpp"
                           "BreakCritLoops.cpp"
                           "BreakInfiniteLoops.cpp"
                           "CheckModule.cpp"
                           "ClassifyInstructions.cpp"
                           "ClassifyLoops.cpp"
                           "CloneMetadata.cpp"
                           "CountInstr.cpp"
                           "DeleteUndefined.cpp"
                           "DummyMarker.cpp"
                           "ExplicitIntLoads.cpp"
                           "ExplicitConsdes.cpp"
                           "FindExits.cpp"
                           "FlattenLoops.cpp"
                           "InitializeUninitialized.cpp"
                           "KInduction.cpp"
                           "InstrumentAlloc.cpp"
                           "InstrumentNontermination.cpp"
                           "InternalizeGlobals.cpp"
                           "MakeNondet.cpp"
                           "Map2CheckLibrary.cpp"
                           "MarkVolatile.cpp"
                           "DeleteCalls.cpp"
                           "GetTestTargets.cpp"
                           "PrepareOverflows.cpp"
                           "RemoveErrorCalls.cpp"
                           "RemoveConstantExprs.cpp"
                           "RemoveInfiniteLoops.cpp"
                           "RenameClamAssume.cpp"
                           "ReplaceReachError.cpp"
)

# Build without runtime type info. Otherwise opt will complain.
target_compile_options(KleeBMCPasses PRIVATE "-fno-rtti")

install(TARGETS KleeBMCPasses LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})
