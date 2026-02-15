MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
REPO_DIR := $(abspath $(MAKEFILE_DIR)/..)
WAVELET := $(REPO_DIR)/target/debug/wavelet

TEST_NAMES := $(basename $(notdir $(patsubst %/,%,$(dir $(wildcard tests/*/test.rs)))))

.PHONY: default
default: tests

# Do not delete intermediate files
.SECONDARY:

build/circt/Makefile: circt
	mkdir -p build/circt
	cmake circt/llvm/llvm -B build/circt \
		-DCMAKE_BUILD_TYPE=RelWithDebInfo \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS=mlir \
		-DLLVM_EXTERNAL_PROJECTS=circt \
		-DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=circt \
		-DLLVM_ENABLE_LLD=ON

# Polygeist uses an older version of LLVM, so unfortunately
# we have to build LLVM and MLIR twice.
build/polygeist/Makefile: polygeist
	mkdir -p build/polygeist
	cmake polygeist/llvm-project/llvm -B build/polygeist \
		-DCMAKE_BUILD_TYPE=RelWithDebInfo \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS="mlir;clang" \
		-DLLVM_EXTERNAL_PROJECTS=polygeist \
		-DLLVM_EXTERNAL_POLYGEIST_SOURCE_DIR=polygeist \
		-DLLVM_ENABLE_LLD=OFF \
		-DLLVM_USE_LINKER=lld \
		-DPOLYGEIST_USE_LINKER=lld

# Build CIRCT/hlstool
build/circt/bin/hlstool: build/circt/Makefile
	cmake --build build/circt --target hlstool --parallel

# Build Polygeist
build/polygeist/bin/cgeist: build/polygeist/Makefile
	cmake --build build/polygeist --target cgeist --parallel

# Build Wavelet
$(WAVELET): $(REPO_DIR)/wavelet $(REPO_DIR)/wavelet-core $(REPO_DIR)/wavelet-elab
	cd $(REPO_DIR) && cargo build

.PHONY: build
build: $(WAVELET) build/circt/bin/hlstool

%.dfg.json: %.rs
	$(WAVELET) compile $< -o $@

# Compile tests from Wavelet/Rust to CIRCT/Handshake
%.handshake.mlir: %.dfg.json
	$(WAVELET) handshake $< -o $@

# Compile CIRCT/Handshake to SystemVerilog
%.sv: %.handshake.mlir
	build/circt/bin/hlstool $< \
		--dynamic-hw \
		--buffering-strategy=all \
		--verilog \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Generates a cocotb Makefile for each test
tests/%/cocotb.makefile:
	echo "SIM ?= icarus" > $@
	echo "TOPLEVEL_LANG ?= verilog" >> $@
	echo "VERILOG_SOURCES += tests/$*/test.sv" >> $@
	echo "COCOTB_TOPLEVEL = top" >> $@
	echo "COCOTB_TEST_MODULES = tests.$*.test" >> $@
	echo "COCOTB_RESULTS_FILE = tests/$*/results.xml" >> $@
	echo "SIM_BUILD = tests/$*/sim_build" >> $@
	echo "include \$$(shell cocotb-config --makefiles)/Makefile.sim" >> $@

.venv/bin/activate: requirements.txt
	python3 -m venv .venv
	. .venv/bin/activate && pip install -r requirements.txt

.PHONY: test-%
test-%: .venv/bin/activate tests/%/cocotb.makefile
	@echo "NOTE: use ctrl + \ to interrupt."
	@$(MAKE) tests/$*/test.sv
	@rm -f tests/$*/results.xml
	@. .venv/bin/activate && make -f tests/$*/cocotb.makefile sim

.PHONY: tests
tests:
	@echo "NOTE: use ctrl + \ to interrupt."; echo
	@PASS=0; FAIL=0; \
	for name in $(TEST_NAMES); do \
		printf "$$name ..."; \
		if $(MAKE) test-$$name > tests/$$name/test.log 2>&1; then \
			echo " PASS"; \
			PASS=$$((PASS + 1)); \
		else \
			echo " FAIL"; \
			echo "============== log =============="; \
			cat tests/$$name/test.log; \
			echo "================================="; \
			FAIL=$$((FAIL + 1)); \
		fi; \
	done; \
	echo; echo "passed: $$PASS, failed: $$FAIL"; \
	if [ $$FAIL -ne 0 ]; then \
		exit 1; \
	fi

.PHONY: clean
clean:
	rm -rf tests/*/*.sv \
		tests/*/*.handshake.mlir \
		tests/*/*.dfg.json \
		tests/*/cocotb.makefile \
		tests/*/results.xml \
		tests/*/sim_build
