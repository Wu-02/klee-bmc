PHASE="building KLEE-BMC"
mkdir -p build-${LLVM_VERSION}-${BUILD_TYPE}
pushd build-${LLVM_VERSION}-${BUILD_TYPE}

# if [ ! -d CMakeFiles ]; then
cmake .. \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DENABLE_REGRESSION=ON \
  -DCMAKE_C_COMPILER=$LLVM_PREFIX/bin/clang \
  -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
  -DCMAKE_INSTALL_PREFIX=$PREFIX \
  -DCMAKE_INSTALL_LIBDIR:PATH=$LLVM_PREFIX/lib \
  -DLLVM_DIR=$LLVM_DIR ||
  exitmsg "Configuring KLEE-BMC"
# fi

(build && install) || exitmsg "Installing KLEE-BMC"
popd

if [ "$(pwd)" != $ABS_SRCDIR ]; then
  exitmsg "Inconsistency in the build script, should be in $ABS_SRCDIR"
fi
