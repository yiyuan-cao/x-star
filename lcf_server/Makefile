export HOLLIGHT_DIR = $(shell pwd)/hol-light
export HOLLIGHT_USE_MODULE = 0

DEBUG ?= 0
ifeq ($(DEBUG), 1)
	PROFILE = debug
else
	PROFILE = release
endif

TARGET_DIR = target/$(PROFILE)
HOL_RPC_SRC = $(shell find hol-rpc/src -name '*.rs')
PROOF_KERNEL_SRC = $(shell find proof-kernel/src -name '*.rs') $(shell find proof-kernel/src -name '*.c')

BDWGC_FLAGS = $(shell pkg-config --libs --cflags bdw-gc)
LIB_CFLAGS = -I$(shell pwd)/includes
ifeq ($(DEBUG), 1)
	LIB_CFLAGS += -g
else
	LIB_CFLAGS += -O3
endif
CFLAGS = $(LIB_CFLAGS) -Lproof-user -L$(TARGET_DIR) $(BDWGC_FLAGS) -lproof_conv -lproof_user -lproof_kernel -lm -std=c2x

############### default ###############

all: default

default: $(TARGET_DIR)/hol-rpc $(TARGET_DIR)/hol-rpc-wrapper compile_flags.txt includes/proof-kernel.h

############### proof-user ###############

compile_flags.txt:
	echo $(CFLAGS) > compile_flags.txt

includes/proof-kernel.h: $(PROOF_KERNEL_SRC) proof-kernel/cbindgen.toml
	cbindgen --config proof-kernel/cbindgen.toml --crate proof-kernel --output includes/proof-kernel.h

$(TARGET_DIR)/libproof_kernel.a: $(PROOF_KERNEL_SRC)
	cargo build --release -p proof-kernel

proof-user/libproof_user.a: proof-user/*.c includes/*.h includes/proof-kernel.h
	clang -c -o proof-user/proof_user.o proof-user/proof-user.c $(LIB_CFLAGS)
	ar rcs proof-user/libproof_user.a proof-user/proof_user.o

proof-conv/libproof_conv.a: proof-user/*.c includes/*.h proof-user/libproof_user.a includes/proof-kernel.h
	clang -c -o proof-user/proof-conv.o proof-user/proof-conv.c $(LIB_CFLAGS)
	ar rcs proof-user/libproof_conv.a proof-user/proof-conv.o 

test: test.c proof-conv/libproof_conv.a proof-user/libproof_user.a includes/proof-kernel.h $(TARGET_DIR)/libproof_kernel.a
	clang -o test test.c $(CFLAGS)

############### proof-kernel ###############

$(TARGET_DIR)/hol-rpc: $(HOL_RPC_SRC) hol-light/pa_j.cmo
	cargo build --bin hol-rpc --release

$(TARGET_DIR)/hol-rpc-wrapper: $(HOL_RPC_SRC)
	cargo build --bin hol-rpc-wrapper --release

############### hol-light ###############

hol-light/pa_j.cmo:
	cd hol-light && make pa_j.cmo

############### targets ###############

.PHONY: clean run run-server run-simple run-simple-client

run: $(TARGET_DIR)/hol-rpc $(TARGET_DIR)/hol-rpc-wrapper
	$(TARGET_DIR)/hol-rpc-wrapper $(TARGET_DIR)/hol-rpc

run-server: $(TARGET_DIR)/hol-rpc
	$(TARGET_DIR)/hol-rpc

clean:
	cd hol-light && make clean
	cargo clean
	rm -f includes/proof-kernel.h
	rm -f examples/output.c
	rm -f reverse
	rm -f simple

