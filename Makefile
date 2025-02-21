CUR_DIR = $(shell pwd)
SRC_DIR := $(CUR_DIR)/src
BUILD_DIR := $(CUR_DIR)/build
BUILD_TYPE := $(BUILD_TYPE:=Release)

include Makefile.inc

NPROC := $(shell nproc)

build_ka_func = \
    (mkdir -p ${2} \
        && cd ${2} \
        && PATH=${LLVM_BUILD}/bin:${PATH} \
            LLVM_ROOT_DIR=${LLVM_BUILD}/bin \
            LLVM_LIBRARY_DIRS=${LLVM_BUILD}/lib \
            LLVM_INCLUDE_DIRS=${LLVM_BUILD}/include \
            CC=clang CXX=clang++ \
            cmake ${1} -DCMAKE_BUILD_TYPE=${BUILD_TYPE} \
        && make -j${NPROC})

all: KAMain tests

KAMain:
	$(call build_ka_func, $(SRC_DIR), $(BUILD_DIR))

tests: KAMain
	@echo "Copying tests from $(SRC_DIR)/tests to $(BUILD_DIR)/tests"
	rm -rf $(BUILD_DIR)/tests
	cp -r $(SRC_DIR)/tests $(BUILD_DIR)