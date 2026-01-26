MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
REPO_DIR := $(abspath $(MAKEFILE_DIR)/..)
WAVELET := $(REPO_DIR)/target/debug/wavelet

TEST_NAMES := $(basename $(notdir $(wildcard tests/*/*.rs)))
ALL_RESULTS := $(addsuffix /results.xml,$(addprefix tests/,$(TEST_NAMES)))

# Configure CIRCT/LLVM
build/Makefile: circt
	cmake circt/llvm/llvm -B build \
		-DCMAKE_BUILD_TYPE=RelWithDebInfo \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS=mlir \
		-DLLVM_EXTERNAL_PROJECTS=circt \
		-DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=circt \
		-DLLVM_ENABLE_LLD=ON

# Build CIRCT/hlstool
build/bin/hlstool: build/Makefile
	cmake --build build --target hlstool --parallel

# Build Wavelet
$(WAVELET): $(REPO_DIR)/wavelet $(REPO_DIR)/wavelet-core $(REPO_DIR)/wavelet-elab
	cd $(REPO_DIR) && cargo build

# Compile tests from Wavelet/Rust to CIRCT/Handshake
%.handshake.mlir: %.rs $(WAVELET)
	$(WAVELET) compile $< --target handshake -o $@

# Compile CIRCT/Handshake to SystemVerilog
%.sv: %.handshake.mlir build/bin/hlstool
	build/bin/hlstool $< \
		--dynamic-hw \
		--buffering-strategy=cycles \
		--verilog \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp
	mv $@.tmp $@

# Generates a cocotb Makefile for each test
tests/%/cocotb.makefile:
	echo "SIM ?= icarus" > $@
	echo "TOPLEVEL_LANG ?= verilog" >> $@
	echo "VERILOG_SOURCES += tests/$*/$*.sv" >> $@
	echo "COCOTB_TOPLEVEL = top" >> $@
	echo "COCOTB_TEST_MODULES = tests.$*.$*" >> $@
	echo "COCOTB_RESULTS_FILE = tests/$*/results.xml" >> $@
	echo "include \$$(shell cocotb-config --makefiles)/Makefile.sim" >> $@

.venv/bin/activate: requirements.txt
	python3 -m venv .venv
	source .venv/bin/activate && pip install -r requirements.txt

tests/%/results.xml: .venv/bin/activate tests/%/cocotb.makefile tests/%/*.sv
	@echo "================== testing $* =================="
	source .venv/bin/activate && make -f tests/$*/cocotb.makefile tests/$*/results.xml
	rm -f tests/$*/results.xml
	@echo "================== completed $* =================="

.PHONY: all-tests
all-tests: $(ALL_RESULTS)
	@echo "all tests passed"
