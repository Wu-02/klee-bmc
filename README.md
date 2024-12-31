# KLEE-BMC: 面向程序分析的局部搜索技术

[![.github/workflows/build_ubuntu.yml](https://github.com/Wu-02/klee-bmc/actions/workflows/build_ubuntu.yml/badge.svg)](https://github.com/Wu-02/klee-bmc/actions/workflows/build_ubuntu.yml)

KLEE-BMC 是一个 C 程序断言判定原型工具，通过将传统的符号执行方法与基于局部搜索、抽象解释、k-归纳的启发式策略相结合，提升符号执行在断言判定 任务中的性能表现。

## 构建

本项目只支持 Ubuntu 系统，可以直接使用 docker 构建项目：
```shell
docker build .
```
也可以按照如下流程构建：
### 1. 安装依赖

首先，使用 `llvm.org` 提供的脚本安装 LLVM-14：
```shell
apt-get update && apt-get install -y wget software-properties-common lsb-release gnupg
wget https://apt.llvm.org/llvm.sh && chmod +x llvm.sh && ./llvm.sh 14
```
然后安装其他依赖：
```shell
apt-get install -y curl rsync make cmake unzip gcc-multilib xz-utils zlib1g-dev \
git build-essential ninja-build pkg-config m4 zlib1g-dev libsqlite3-dev \
libboost-all-dev libgmp-dev pip
# HACK: see https://github.com/llvm/llvm-project/issues/59903
apt-get download libpolly-14-dev && dpkg --force-all -i libpolly-14-dev*
```
然后通过 pip 安装 meson 和 lit，用于 KLEE 的构建与测试：

（注：Ubuntu24.04 及之后的系统可能无法使用以下命令安装，可以使用 pipx 代替 pip 全局安装，或者安装到 venv 虚拟环境）
```shell
pip install meson lit
```

### 2. 运行构建脚本

切换到项目根目录，运行如下命令，即可将工具安装到指定路径下：
```shell
cd <source-root>
./build.sh --targets=all --llvm-dir=/usr/lib/llvm-14 --prefix=<path-to-install>
```
如果未提供安装路径，将会默认安装到项目根目录下的 `Release` 文件夹中。

## 运行

切换到可执行文件目录：
```shell
cd <path-to-install>/bin
```

判定 `file.c` 中的断言错误是否能被触发：
```shell
./klee-bmc file.c -o test_case
```
工具输出 `test_case` 为触发断言的输入字节流。程序中所有未定义函数调用的返回值都被视为输入。

查看工具的可用参数：
```shell
./klee-bmc --help
```
