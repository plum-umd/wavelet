SHELL := /bin/bash -o pipefail
TEST_NAMES := $(basename $(notdir $(patsubst %/,%,$(dir $(wildcard tests/*/test.rs)))))

CGEIST := build/polygeist/bin/cgeist
HLSTOOL := build/circt/bin/hlstool
WAVELET := ../target/release/wavelet
WAVELET_COMPILE_FLAGS :=

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
		-DCMAKE_BUILD_TYPE=RelWithDeb \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS=mlir \
		-DLLVM_EXTERNAL_PROJECTS=circt \
		-DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=circt \
		-DLLVM_ENABLE_LLD=ON \
		-DLLVM_PARALLEL_LINK_JOBS=1

# Build CIRCT/hlstool
$(HLSTOOL): build/circt/Makefile
	$(MAKE) -C build/circt hlstool

# Polygeist uses an older version of LLVM, so unfortunately
# we have to build LLVM and MLIR twice.
build/polygeist/Makefile: polygeist
	mkdir -p build/polygeist
	cmake polygeist/llvm-project/llvm -B build/polygeist \
		-DCMAKE_BUILD_TYPE=RelWithDeb \
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
	$(MAKE) -C build/polygeist cgeist

# Build Dynamatic (using its Docker image)
# TODO: Experimental
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

build/prjtrellis/install: build/prjtrellis/Makefile
	$(MAKE) -C build/prjtrellis
	cmake --install build/prjtrellis

# Configure and build nextpnr-ecp5
build/nextpnr/Makefile: nextpnr build/prjtrellis/install
	mkdir -p build/nextpnr
	cmake nextpnr -B build/nextpnr \
		-DARCH=ecp5 \
		-DTRELLIS_INSTALL_PREFIX=$(realpath build/prjtrellis/install)

build/nextpnr/nextpnr-ecp5: build/nextpnr/Makefile
	$(MAKE) -C build/nextpnr nextpnr-ecp5

build/verilator/bin/verilator: verilator
	mkdir -p build/verilator
	cd verilator && \
		autoconf && \
		./configure --prefix=$(realpath build/verilator) && \
		$(MAKE) && $(MAKE) install

build/yosys/yosys: yosys
	mkdir -p build/yosys
	cd build/yosys && $(MAKE) -f $(realpath yosys/Makefile)

#################################
# Various compilation pipelines #
#################################

%.wavelet.json: %.rs
	$(WAVELET) compile $< $(WAVELET_COMPILE_FLAGS) -o $@ 2>&1 | tee $@.log

%.wavelet-noopt.json: %.rs
	$(WAVELET) compile $< --no-opt $(WAVELET_COMPILE_FLAGS) -o $@ 2>&1 | tee $@.log

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
	$(CGEIST) -O3 --memref-fullrank -S $< | \
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

# Test Wavelet-generated design
.PHONY: wavelet-test-%
wavelet-test-%: tests/%/test.wavelet.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@python3 -m sim \
		tests/$*/test.wavelet.sv \
		tests/$*/test.py \
		--interface wavelet \
		--top top 2>&1 | tee tests/$*/test.wavelet.log

# Test Wavelet-generated design (without optimizations)
.PHONY: wavelet-noopt-test-%
wavelet-noopt-test-%: tests/%/test.wavelet-noopt.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@python3 -m sim \
		tests/$*/test.wavelet-noopt.sv \
		tests/$*/test.py \
		--interface wavelet \
		--top top 2>&1 | tee tests/$*/test.wavelet-noopt.log

# Test Polygeist-CIRCT-generated design
.PHONY: circt-test-%
circt-test-%: tests/%/test.circt.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@python3 -m sim \
		tests/$*/test.circt.sv \
		tests/$*/test.py \
		--interface circt \
		--top $* 2>&1 | tee tests/$*/test.circt.log

# Test Wavelet-generated design, but using high-level dataflow simulation
.PHONY: wavelet-sim-test-%
wavelet-sim-test-%: tests/%/test.wavelet.json
	@python3 -m sim \
		tests/$*/test.wavelet.json \
		tests/$*/test.py \
		--interface wavelet-sim 2>&1 | tee tests/$*/test.wavelet-sim.log

# Test (unoptimized) Wavelet-generated design, but using high-level dataflow simulation
.PHONY: wavelet-noopt-sim-test-%
wavelet-noopt-sim-test-%: tests/%/test.wavelet-noopt.json
	@python3 -m sim \
		tests/$*/test.wavelet-noopt.json \
		tests/$*/test.py \
		--interface wavelet-sim 2>&1 | tee tests/$*/test.wavelet-noopt-sim.log

# Test RipTide-compiled design using high-level dataflow simulation
.PHONY: riptide-sim-test-%
riptide-sim-test-%: tests/%/test.riptide.json
	@python3 -m sim \
		tests/$*/test.riptide.json \
		tests/$*/test.py \
		--interface riptide-sim 2>&1 | tee tests/$*/test.riptide-sim.log

# Test RipTide-compiled design (no-stream version) using high-level dataflow simulation
.PHONY: riptide-sim-nostream-test-%
riptide-sim-nostream-test-%: tests/%/test.riptide.nostream.json
	@python3 -m sim \
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
	@pass=0; fail=0; log=$$(mktemp); \
	for name in $(TEST_NAMES); do \
		printf "[$*] $$name ..."; \
		if $(MAKE) $*-test-$$name > "$$log" 2>&1; then \
			echo " PASS"; \
			pass=$$((pass + 1)); \
		else \
			echo " FAIL"; \
			echo "============== log =============="; \
			cat "$$log"; \
			echo "================================="; \
			fail=$$((fail + 1)); \
		fi; \
	done; \
	rm -f "$$log"; \
	echo "[$*] $$pass passed, $$fail failed"; \
	if [ $$fail -ne 0 ]; then \
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
	@success=0; fail=0; \
	for name in $(TEST_NAMES); do \
		printf "[$*-pnr] $$name ..."; \
		if $(MAKE) tests/$$name/test.$*.nextpnr.json > /dev/null 2>&1; then \
			echo " SUCCESS"; \
			success=$$((success + 1)); \
		else \
			echo " FAIL"; \
			fail=$$((fail + 1)); \
		fi; \
	done; \
	echo "[$*-pnr] $$success succeeded, $$fail failed"; \
	if [ $$fail -ne 0 ]; then \
		exit 1; \
	fi

.PHONY: clean
clean:
	rm -rf \
		tests/*/*.sv \
		tests/*/*.v \
		tests/*/*.mlir \
		tests/*/*.wavelet.json \
		tests/*/*.wavelet-noopt.json \
		tests/*/*.netlist.json \
		tests/*/*.nextpnr.json \
		tests/*/*.log \
		tests/*/*.tmp

###################################
# Targets for artifact evaluation #
###################################

EVAL_NAMES := \
	dither \
	dmm \
	dmv \
	nn-conv \
	nn-fc \
	nn-norm \
	nn-pool \
	nn-relu \
	nn-vadd \
	sort

# Skip some targets that are expected to fail
SKIP_TARGETS := circt-eval-sort

# $(1): label, $(2): test name, $(3): sub-make targets
define run-eval
	$(if $(filter $(1)-eval-$(2),$(SKIP_TARGETS)),\
		@echo "[$(1)] $(2) ... SKIP",\
		@log=$$(mktemp); \
		if $(MAKE) --no-print-directory WAVELET_COMPILE_FLAGS="$(WAVELET_COMPILE_FLAGS)" $(3) > "$$log" 2>&1; then \
			echo "[$(1)] $(2) ... PASS"; \
		else \
			echo "[$(1)] $(2) ... FAIL"; \
			echo "============== log =============="; \
			cat "$$log"; \
			echo "================================="; \
			rm -f "$$log"; \
			exit 1; \
		fi; \
		rm -f "$$log")
endef

.PHONY: \
	wavelet-compile-% \
	wavelet-noopt-compile-% \
	wavelet-eval-% \
	wavelet-noopt-eval-% \
	circt-eval-% \
	wavelet-sim-eval-% \
	wavelet-noopt-sim-eval-% \
	riptide-sim-eval-%

wavelet-compile-%: WAVELET_COMPILE_FLAGS := --ghost-check
wavelet-compile-%:
	$(call run-eval,wavelet,$*,tests/$*/test.wavelet.json)

wavelet-noopt-compile-%:
	$(call run-eval,wavelet-noopt,$*,tests/$*/test.wavelet-noopt.json)

wavelet-eval-%: WAVELET_COMPILE_FLAGS := --ghost-check
wavelet-eval-%:
	$(call run-eval,wavelet,$*,wavelet-test-$* wavelet-sim-test-$* tests/$*/test.wavelet.nextpnr.json)

wavelet-noopt-eval-%:
	$(call run-eval,wavelet-noopt,$*,wavelet-noopt-test-$* wavelet-noopt-sim-test-$* tests/$*/test.wavelet-noopt.nextpnr.json)

circt-eval-%:
	$(call run-eval,circt,$*,circt-test-$* tests/$*/test.circt.nextpnr.json)

riptide-eval-%:
	$(call run-eval,riptide,$*,riptide-sim-test-$*)

# Run all evaluations
eval: $(foreach name,$(EVAL_NAMES), \
	wavelet-eval-$(name) \
	wavelet-noopt-eval-$(name) \
	circt-eval-$(name) \
	riptide-eval-$(name) \
)

# Only run relevant Wavelet compilation targets
# Used for better performance estimates.
eval-compile: $(foreach name,$(EVAL_NAMES), \
	wavelet-compile-$(name) \
	wavelet-noopt-compile-$(name) \
)
