PHASE="building KLEE-BMC"
mkdir -p build-${LLVM_VERSION}-${BUILD_TYPE}
pushd build-${LLVM_VERSION}-${BUILD_TYPE}

cmake .. \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
  -DCMAKE_INSTALL_PREFIX=$PREFIX \
  -DCMAKE_INSTALL_LIBDIR:PATH=$LLVM_PREFIX/lib ||
  exitmsg "Configuring KLEE-BMC"

(build && install) || exitmsg "Installing KLEE-BMC"
popd
