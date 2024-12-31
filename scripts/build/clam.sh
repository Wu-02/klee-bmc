PHASE="building Clam"
if [ "x$UPDATE" = "x1" -o -z "$(ls -A $SRCDIR/clam-build)" ]; then
  rm -rf clam-build
  git clone --depth=1 https://github.com/Wu-02/clam-kind.git clam-build
fi

mkdir -p clam-build/build-${LLVM_VERSION}-${BUILD_TYPE}
pushd clam-build/build-${LLVM_VERSION}-${BUILD_TYPE}

cmake .. \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DLLVM_DIR=$LLVM_DIR \
  -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
  -DCMAKE_INSTALL_PREFIX=$LLVM_PREFIX \
  -DCMAKE_INSTALL_LIBDIR:PATH=$LLVM_PREFIX/lib \
  -DCLAM_LIBS_TYPE=SHARED ||
  clean_and_exit 1

if [ ! -d crab ]; then
  (cmake --build . --target crab $JOBS_ARG && cmake ..) || clean_and_exit 1
fi

if [ ! -d llvm-seahorn ]; then
  (cmake --build . --target extra $JOBS_ARG && cmake ..) || clean_and_exit 1
fi

(cmake --build . --target install $JOBS_ARG) || clean_and_exit 1
popd
