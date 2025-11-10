MAKEFILE_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
REPO_DIR := $(MAKEFILE_DIR)/..

SDC := python3 -m tools.sdc
SDC_FLAGS := --lib-dc ${LIBDC_PATH} \
			 --llvm-bin ${LLVM_12_BIN} \
			 --bisim \
			 --bisim-permission-unsat-core \
			 --bisim-cut-point-expansion \
			 --bisim-permission-fractional-reads 4

SOURCES := $(wildcard *.c)
TARGETS := $(SOURCES:%.c=%.bisim.out)

.PHONY: all
all: $(TARGETS)

.PHONY: show_results
show_results: $(TARGETS)
	grep -E "bisim check took|confluence check took|confluence check result" *.bisim.out

%.bisim.out: %.c
	cd $(REPO_DIR) && $(SDC) $(SDC_FLAGS) $(MAKEFILE_DIR)/$< 1>&2 2>$(MAKEFILE_DIR)/$@

.PHONY: clean
clean:
	rm -f *.lso.ll *.o2p *.out
