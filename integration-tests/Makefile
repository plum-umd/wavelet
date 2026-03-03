MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
REPO_DIR := $(abspath $(MAKEFILE_DIR)/..)
WAVELET := $(REPO_DIR)/target/release/wavelet
CGEIST := $(REPO_DIR)/integration-tests/build/polygeist/bin/cgeist
HLSTOOL := $(REPO_DIR)/integration-tests/build/circt/bin/hlstool

TEST_NAMES := $(basename $(notdir $(patsubst %/,%,$(dir $(wildcard tests/*/test.rs)))))

.PHONY: default
default: wavelet-tests

# Do not delete intermediate files
.SECONDARY:

#################################
# Rules to build required tools #
#################################

.PHONY: build
build: $(WAVELET) $(HLSTOOL)

build/circt/Makefile: circt
	mkdir -p build/circt
	cmake circt/llvm/llvm -B build/circt \
		-DCMAKE_BUILD_TYPE=RelWithDebInfo \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS=mlir \
		-DLLVM_EXTERNAL_PROJECTS=circt \
		-DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=circt \
		-DLLVM_ENABLE_LLD=ON \
		-DLLVM_PARALLEL_LINK_JOBS=1

# Build CIRCT/hlstool
$(HLSTOOL): build/circt/Makefile
	cmake --build build/circt --target hlstool --parallel

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
		-DPOLYGEIST_USE_LINKER=lld \
		-DLLVM_PARALLEL_LINK_JOBS=1

# Build Polygeist
build/polygeist/bin/cgeist: build/polygeist/Makefile
	cmake --build build/polygeist --target cgeist --parallel

# Build Dynamatic (using its Docker image)
dynamatic/bin/dynamatic:
	docker build -t dynamatic-build dynamatic
	docker run -it -v $(realpath dynamatic):/dynamatic -w /dynamatic dynamatic-build ./build.sh

# Build Wavelet
$(WAVELET): $(REPO_DIR)/wavelet $(REPO_DIR)/wavelet-core $(REPO_DIR)/wavelet-elab
	cd $(REPO_DIR) && cargo build --release

# Configure and build prjtrellis
build/prjtrellis/Makefile: prjtrellis
	mkdir -p build/prjtrellis
	cmake prjtrellis/libtrellis -B build/prjtrellis \
		-DCMAKE_INSTALL_PREFIX=build/prjtrellis/install

build/prjtrellis/install/bin/ecpbram: build/prjtrellis/Makefile
	cmake --build build/prjtrellis --parallel
	cmake --install build/prjtrellis

# Configure and build nextpnr-ecp5
build/nextpnr/Makefile: nextpnr
	mkdir -p build/nextpnr
	cmake nextpnr -B build/nextpnr \
		-DARCH=ecp5 \
		-DTRELLIS_INSTALL_PREFIX=$(realpath build/prjtrellis/install)

build/nextpnr/nextpnr-ecp5: build/nextpnr/Makefile
	cmake --build build/nextpnr --target nextpnr-ecp5 --parallel

#################################
# Various compilation pipelines #
#################################

%.wavelet.json: %.rs
	$(WAVELET) compile $< -o $@ 2>&1 | tee $@.log

%.wavelet-noopt.json: %.rs
	$(WAVELET) compile $< --no-opt -o $@ 2>&1 | tee $@.log

# Compile tests from Wavelet/Rust to CIRCT/Handshake
%.wavelet.handshake.mlir: %.wavelet.json
	$(WAVELET) handshake $< -o $@

%.wavelet-noopt.handshake.mlir: %.wavelet-noopt.json
	$(WAVELET) handshake $< -o $@

# Compile CIRCT/Handshake to SystemVerilog
%.wavelet.sv: %.wavelet.handshake.mlir
	$(HLSTOOL) $< \
		--verilog \
		--dynamic-hw \
		--buffering-strategy=cycles \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

%.wavelet-noopt.sv: %.wavelet-noopt.handshake.mlir
	$(HLSTOOL) $< \
		--verilog \
		--dynamic-hw \
		--buffering-strategy=cycles \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Compile C to MLIR/scf through Polygeist
%.circt.scf.mlir: %.c
	build/polygeist/bin/cgeist -O3 --memref-fullrank -S $< | \
		sed -E 's/[[:space:]]*attributes[[:space:]]*\{[^}]*\}//g' > $@.tmp \
		|| (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Compile MLIR/scf to CIRCT/Handshake
%.circt.handshake.mlir: %.circt.scf.mlir
	$(HLSTOOL) $< \
		--ir --output-level=core \
		--dynamic-hw \
		--buffering-strategy=cycles \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Compile MLIR/scf to SystemVerilog
%.circt.sv: %.circt.scf.mlir
	$(HLSTOOL) $< \
		--verilog \
		--dynamic-hw \
		--buffering-strategy=cycles \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Convert to Verilog to resolve any unsupported SystemVerilog constructs
%.v: %.sv
	sv2v $< > $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

# Synthesis with Yosys
%.netlist.json: %.v
	yosys -p "read_verilog $<; synth_ecp5 -json $@" > $@.log 2>&1

# Placement and routing
%.nextpnr.json: %.netlist.json
	build/nextpnr/nextpnr-ecp5 \
		--json $< \
		--um-85k \
		--package CABGA756 \
		--speed 6 \
		--out-of-context \
		--timing-allow-fail \
		--lpf-allow-unconstrained \
		--write $@ > $@.log 2>&1

######################
# End-to-end testing #
######################

.venv/bin/activate: requirements.txt
	python3 -m venv .venv
	. .venv/bin/activate && pip install -r requirements.txt

# Test Wavelet-generated design
.PHONY: test-wavelet-%
test-wavelet-%: .venv/bin/activate tests/%/test.wavelet.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.wavelet.sv \
		tests/$*/test.py \
		--interface wavelet \
		--top top 2>&1 | tee tests/$*/test.wavelet.log

# Test Wavelet-generated design (without optimizations)
.PHONY: test-wavelet-noopt-%
test-wavelet-noopt-%: .venv/bin/activate tests/%/test.wavelet-noopt.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.wavelet-noopt.sv \
		tests/$*/test.py \
		--interface wavelet \
		--top top 2>&1 | tee tests/$*/test.wavelet-noopt.log

# Test Polygeist-CIRCT-generated design
.PHONY: test-circt-%
test-circt-%: .venv/bin/activate tests/%/test.circt.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.circt.sv \
		tests/$*/test.py \
		--interface circt \
		--top $* 2>&1 | tee tests/$*/test.circt.log

# Test Wavelet-generated design, but using high-level dataflow simulation
.PHONY: test-wavelet-sim-%
test-wavelet-sim-%: .venv/bin/activate tests/%/test.wavelet.json
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.wavelet.json \
		tests/$*/test.py \
		--interface wavelet-sim 2>&1 | tee tests/$*/test.wavelet-sim.log

# Test (unoptimized) Wavelet-generated design, but using high-level dataflow simulation
.PHONY: test-wavelet-noopt-sim-%
test-wavelet-noopt-sim-%: .venv/bin/activate tests/%/test.wavelet-noopt.json
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.wavelet-noopt.json \
		tests/$*/test.py \
		--interface wavelet-sim 2>&1 | tee tests/$*/test.wavelet-noopt-sim.log

# Test RipTide-compiled design using high-level dataflow simulation
.PHONY: test-riptide-sim-%
test-riptide-sim-%: .venv/bin/activate tests/%/test.riptide.json
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.riptide.json \
		tests/$*/test.py \
		--interface riptide-sim 2>&1 | tee tests/$*/test.riptide-sim.log

# Test RipTide-compiled design (no-stream version) using high-level dataflow simulation
.PHONY: test-riptide-sim-%
test-riptide-sim-nostream-%: .venv/bin/activate tests/%/test.riptide.nostream.json
	@set -eu -o pipefail; \
	. .venv/bin/activate && python3 -m sim \
		tests/$*/test.riptide.nostream.json \
		tests/$*/test.py \
		--interface riptide-sim 2>&1 | tee tests/$*/test.riptide-sim.nostream.log

# Run all available tests for a given pipeline
.PHONY: %-tests
%-tests:
	@if [ "$*" != "wavelet" ] && \
		[ "$*" != "wavelet-noopt" ] && \
		[ "$*" != "wavelet-sim" ] && \
		[ "$*" != "wavelet-noopt-sim" ] && \
		[ "$*" != "riptide-sim" ] && \
		[ "$*" != "circt" ]; then \
		echo "unknown pipeline: $*"; \
		exit 1; \
	fi
	@echo "using pipeline: $*"
	@echo "NOTE: use ctrl + \ to interrupt."; echo
	@PASS=0; FAIL=0; \
	for name in $(TEST_NAMES); do \
		printf "$$name ..."; \
		if $(MAKE) test-$*-$$name > /dev/null 2>&1; then \
			echo " PASS"; \
			PASS=$$((PASS + 1)); \
		else \
			echo " FAIL"; \
			echo "============== log =============="; \
			cat tests/$$name/test.$*.log; \
			echo "================================="; \
			FAIL=$$((FAIL + 1)); \
		fi; \
	done; \
	echo; echo "passed: $$PASS, failed: $$FAIL"; \
	if [ $$FAIL -ne 0 ]; then \
		exit 1; \
	fi

# Place and route all tests
.PHONY: %-pnr
%-pnr:
	@if [ "$*" != "wavelet" ] && \
		[ "$*" != "wavelet-noopt" ] && \
		[ "$*" != "circt" ]; then \
		echo "unknown pipeline for placement and routing: $*"; \
		exit 1; \
	fi
	@echo "using pipeline: $*"; echo
	@SUCCESS=0; FAIL=0; \
	for name in $(TEST_NAMES); do \
		printf "$$name ..."; \
		if $(MAKE) tests/$$name/test.$*.nextpnr.json > /dev/null 2>&1; then \
			echo " SUCCESS"; \
			SUCCESS=$$((SUCCESS + 1)); \
		else \
			echo " FAIL"; \
			FAIL=$$((FAIL + 1)); \
		fi; \
	done; \
	echo; echo "succeeded: $$SUCCESS, failed: $$FAIL"; \
	if [ $$FAIL -ne 0 ]; then \
		exit 1; \
	fi

.PHONY: clean
clean:
	rm -rf \
		sim_build \
		tests/*/*.sv \
		tests/*/*.v \
		tests/*/*.mlir \
		tests/*/*.wavelet.json \
		tests/*/*.wavelet-noopt.json \
		tests/*/*.netlist.json \
		tests/*/*.nextpnr.json \
		tests/*/*.log \
		tests/*/*.tmp
