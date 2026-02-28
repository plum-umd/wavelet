MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
REPO_DIR := $(abspath $(MAKEFILE_DIR)/..)
WAVELET := $(REPO_DIR)/target/debug/wavelet
CGEIST := $(REPO_DIR)/integration-tests/build/polygeist/bin/cgeist
HLSTOOL := $(REPO_DIR)/integration-tests/build/circt/bin/hlstool

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
	cd $(REPO_DIR) && cargo build

.PHONY: build
build: $(WAVELET) $(HLSTOOL)

%.wavelet.json: %.rs
	$(WAVELET) compile $< -o $@

# Compile tests from Wavelet/Rust to CIRCT/Handshake
%.wavelet.handshake.mlir: %.wavelet.json
	$(WAVELET) handshake $< -o $@

# Compile CIRCT/Handshake to SystemVerilog
%.wavelet.sv: %.wavelet.handshake.mlir
	$(HLSTOOL) $< \
		--verilog \
		--dynamic-hw \
		--buffering-strategy=all \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

%.circt.scf.mlir: %.c
	build/polygeist/bin/cgeist -O3 --memref-fullrank -S $< | \
		sed -E 's/[[:space:]]*attributes[[:space:]]*\{[^}]*\}//g' > $@.tmp \
		|| (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

%.circt.handshake.mlir: %.circt.scf.mlir
	$(HLSTOOL) $< \
		--ir --output-level=core \
		--dynamic-hw \
		--buffering-strategy=all \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

%.circt.sv: %.circt.scf.mlir
	$(HLSTOOL) $< \
		--verilog \
		--dynamic-hw \
		--buffering-strategy=all \
		--lowering-options=disallowLocalVariables \
		--verify-each \
		--verbose-pass-executions \
		> $@.tmp || (rm -f $@.tmp && exit 1)
	mv $@.tmp $@

.venv/bin/activate: requirements.txt
	python3 -m venv .venv
	. .venv/bin/activate && pip install -r requirements.txt

# Test Wavelet-generated design
.PHONY: test-wavelet-%
test-wavelet-%: .venv/bin/activate tests/%/test.wavelet.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@. .venv/bin/activate && python3 -m sim \
		tests/$*/test.wavelet.sv \
		tests/$*/test.py \
		--interface wavelet \
		--top top

# Test Polygeist-CIRCT-generated design
.PHONY: test-circt-%
test-circt-%: .venv/bin/activate tests/%/test.circt.sv
	@echo "NOTE: use ctrl + \ to interrupt."
	@. .venv/bin/activate && python3 -m sim \
		tests/$*/test.circt.sv \
		tests/$*/test.py \
		--interface circt \
		--top $*

.PHONY: tests
tests: wavelet-tests

# Run equivalence tests using the selected pipline (wavelet/circt)
.PHONY: %-tests
%-tests:
	@if [ "$*" != "wavelet" ] && [ "$*" != "circt" ]; then \
		echo "unknown pipeline: $*"; \
		exit 1; \
	fi
	@echo "using pipeline: $*"
	@echo "NOTE: use ctrl + \ to interrupt."; echo
	@PASS=0; FAIL=0; \
	for name in $(TEST_NAMES); do \
		printf "$$name ..."; \
		if $(MAKE) test-$*-$$name > tests/$$name/test.$*.log 2>&1; then \
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

.PHONY: clean
clean:
	rm -rf tests/*/*.sv \
		tests/*/*.wavelet.handshake.mlir \
		tests/*/*.wavelet.json \
		tests/*/cocotb.makefile \
		tests/*/results.xml \
		tests/*/sim_build \
		tests/*/*.log
