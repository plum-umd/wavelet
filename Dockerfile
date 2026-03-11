# Base build image with all required toolchains
FROM ubuntu:24.04 AS build-base

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get install -y \
        curl build-essential lld git ninja-build \
        cmake libboost-all-dev libeigen3-dev \
        flex bison help2man gawk libffi-dev \
        libfl-dev libreadline-dev tcl-dev

RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --default-toolchain none
RUN curl -fsSL https://get.haskellstack.org/ | sh -s
RUN curl -fsSL https://astral.sh/uv/install.sh | sh -s

ENV PATH="/root/.elan/bin:/root/.cargo/bin:${PATH}"
WORKDIR /wavelet/integration-tests

#  ██████╗██╗██████╗  ██████╗████████╗
# ██╔════╝██║██╔══██╗██╔════╝╚══██╔══╝
# ██║     ██║██████╔╝██║        ██║
# ██║     ██║██╔══██╗██║        ██║
# ╚██████╗██║██║  ██║╚██████╗   ██║
#  ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝   ╚═╝
FROM build-base AS build-circt
RUN git clone https://github.com/llvm/circt.git && \
    git -C circt checkout 894bd8c && \
    git -C circt submodule update --init --recursive --depth=1 --jobs=$(nproc)
RUN mkdir -p build/circt && \
    cmake circt/llvm/llvm -G Ninja -B build/circt \
		-DCMAKE_BUILD_TYPE=Release \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS=mlir \
		-DLLVM_EXTERNAL_PROJECTS=circt \
		-DLLVM_EXTERNAL_CIRCT_SOURCE_DIR=circt \
		-DLLVM_ENABLE_LLD=ON \
		-DLLVM_PARALLEL_LINK_JOBS=1 \
        -DLLVM_INCLUDE_TESTS=OFF \
        -DLLVM_INCLUDE_EXAMPLES=OFF \
        -DLLVM_INCLUDE_BENCHMARKS=OFF \
        -DLLVM_ENABLE_BINDINGS=OFF \
        -DMLIR_INCLUDE_TESTS=OFF && \
    cmake --build build/circt --target hlstool
RUN strip --strip-all build/circt/bin/hlstool && \
    rm -rf circt && \
    mv build build-old && \
    mkdir -p build/circt/bin && \
    mv build-old/circt/bin/hlstool build/circt/bin/hlstool && \
    rm -rf build-old

# ██████╗  ██████╗ ██╗  ██╗   ██╗ ██████╗ ███████╗██╗███████╗████████╗
# ██╔══██╗██╔═══██╗██║  ╚██╗ ██╔╝██╔════╝ ██╔════╝██║██╔════╝╚══██╔══╝
# ██████╔╝██║   ██║██║   ╚████╔╝ ██║  ███╗█████╗  ██║███████╗   ██║
# ██╔═══╝ ██║   ██║██║    ╚██╔╝  ██║   ██║██╔══╝  ██║╚════██║   ██║
# ██║     ╚██████╔╝███████╗██║   ╚██████╔╝███████╗██║███████║   ██║
# ╚═╝      ╚═════╝ ╚══════╝╚═╝    ╚═════╝ ╚══════╝╚═╝╚══════╝   ╚═╝
FROM build-base AS build-polygeist
RUN git clone https://github.com/llvm/Polygeist.git polygeist && \
    git -C polygeist checkout 77c04bb && \
    git -C polygeist submodule update --init --recursive --depth=1 --jobs=$(nproc)
RUN mkdir -p build/polygeist && \
    cmake polygeist/llvm-project/llvm -G Ninja -B build/polygeist \
		-DCMAKE_BUILD_TYPE=Release \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DLLVM_TARGETS_TO_BUILD=host \
		-DLLVM_ENABLE_PROJECTS="mlir;clang" \
		-DLLVM_EXTERNAL_PROJECTS=polygeist \
		-DLLVM_EXTERNAL_POLYGEIST_SOURCE_DIR=polygeist \
		-DLLVM_ENABLE_LLD=OFF \
		-DLLVM_USE_LINKER=lld \
		-DPOLYGEIST_USE_LINKER=lld \
        -DLLVM_INCLUDE_TESTS=OFF \
        -DLLVM_INCLUDE_EXAMPLES=OFF \
        -DLLVM_INCLUDE_BENCHMARKS=OFF \
        -DLLVM_ENABLE_BINDINGS=OFF \
        -DMLIR_INCLUDE_TESTS=OFF && \
    cmake --build build/polygeist --target cgeist
RUN strip --strip-all build/polygeist/bin/cgeist && \
    rm -rf polygeist && \
    mv build build-old && \
    mkdir -p build/polygeist/bin && \
    mv build-old/polygeist/bin/cgeist build/polygeist/bin/cgeist && \
    rm -rf build-old

# ███╗   ██╗███████╗██╗  ██╗████████╗██████╗ ███╗   ██╗██████╗
# ████╗  ██║██╔════╝╚██╗██╔╝╚══██╔══╝██╔══██╗████╗  ██║██╔══██╗
# ██╔██╗ ██║█████╗   ╚███╔╝    ██║   ██████╔╝██╔██╗ ██║██████╔╝
# ██║╚██╗██║██╔══╝   ██╔██╗    ██║   ██╔═══╝ ██║╚██╗██║██╔══██╗
# ██║ ╚████║███████╗██╔╝ ██╗   ██║   ██║     ██║ ╚████║██║  ██║
# ╚═╝  ╚═══╝╚══════╝╚═╝  ╚═╝   ╚═╝   ╚═╝     ╚═╝  ╚═══╝╚═╝  ╚═╝
FROM build-base AS build-nextpnr
RUN git clone https://github.com/YosysHQ/prjtrellis.git && \
    git -C prjtrellis checkout 73bd411 && \
    git -C prjtrellis submodule update --init --recursive --depth=1 --jobs=$(nproc) && \
    git clone https://github.com/YosysHQ/nextpnr.git && \
    git -C nextpnr checkout ab7aa9f && \
    git -C nextpnr submodule update --init --recursive --depth=1 --jobs=$(nproc)
RUN mkdir -p build/prjtrellis build/nextpnr && \
    cmake prjtrellis/libtrellis -G Ninja -B build/prjtrellis \
		-DCMAKE_INSTALL_PREFIX=$(realpath build/prjtrellis/install) && \
    cmake --build build/prjtrellis && \
    cmake --install build/prjtrellis && \
    cmake nextpnr -G Ninja -B build/nextpnr \
		-DARCH=ecp5 \
		-DTRELLIS_INSTALL_PREFIX=$(realpath build/prjtrellis/install) && \
    cmake --build build/nextpnr --target nextpnr-ecp5
RUN strip --strip-all build/nextpnr/nextpnr-ecp5 && \
    rm -rf prjtrellis nextpnr && \
    mv build build-old && \
    mkdir -p build/nextpnr && \
    mv build-old/nextpnr/nextpnr-ecp5 build/nextpnr/nextpnr-ecp5 && \
    rm -rf build-old

# ███████╗██╗   ██╗██████╗ ██╗   ██╗
# ██╔════╝██║   ██║╚════██╗██║   ██║
# ███████╗██║   ██║ █████╔╝██║   ██║
# ╚════██║╚██╗ ██╔╝██╔═══╝ ╚██╗ ██╔╝
# ███████║ ╚████╔╝ ███████╗ ╚████╔╝
# ╚══════╝  ╚═══╝  ╚══════╝  ╚═══╝
FROM build-base AS build-sv2v
RUN git clone https://github.com/zachjs/sv2v.git && \
    git -C sv2v checkout v0.0.13 && \
    make -C sv2v -j$(nproc) && \
    mkdir -p build/sv2v/bin && \
    cp sv2v/bin/sv2v build/sv2v/bin/sv2v
RUN rm -rf sv2v

# ██╗   ██╗ ██████╗ ███████╗██╗   ██╗███████╗
# ╚██╗ ██╔╝██╔═══██╗██╔════╝╚██╗ ██╔╝██╔════╝
#  ╚████╔╝ ██║   ██║███████╗ ╚████╔╝ ███████╗
#   ╚██╔╝  ██║   ██║╚════██║  ╚██╔╝  ╚════██║
#    ██║   ╚██████╔╝███████║   ██║   ███████║
#    ╚═╝    ╚═════╝ ╚══════╝   ╚═╝   ╚══════╝
FROM build-base AS build-yosys
RUN git clone https://github.com/YosysHQ/yosys.git && \
    git -C yosys fetch origin v0.62 && \
    git -C yosys checkout v0.62 && \
    git -C yosys submodule update --init --recursive --depth=1 --jobs=$(nproc) && \
    mkdir -p build/yosys && \
    cd yosys && \
    make -j$(nproc) && \
    make install DESTDIR=$(realpath ../build/yosys) PREFIX=
RUN rm -rf yosys

# ██╗   ██╗███████╗██████╗ ██╗██╗      █████╗ ████████╗ ██████╗ ██████╗
# ██║   ██║██╔════╝██╔══██╗██║██║     ██╔══██╗╚══██╔══╝██╔═══██╗██╔══██╗
# ██║   ██║█████╗  ██████╔╝██║██║     ███████║   ██║   ██║   ██║██████╔╝
# ╚██╗ ██╔╝██╔══╝  ██╔══██╗██║██║     ██╔══██║   ██║   ██║   ██║██╔══██╗
#  ╚████╔╝ ███████╗██║  ██║██║███████╗██║  ██║   ██║   ╚██████╔╝██║  ██║
#   ╚═══╝  ╚══════╝╚═╝  ╚═╝╚═╝╚══════╝╚═╝  ╚═╝   ╚═╝    ╚═════╝ ╚═╝  ╚═╝
FROM build-base AS build-verilator
RUN git clone https://github.com/verilator/verilator.git && \
    git -C verilator checkout v5.044 && \
    git -C verilator submodule update --init --recursive --depth=1 --jobs=$(nproc) && \
    mkdir -p build/verilator && \
	cd verilator && \
    autoconf && \
    ./configure --prefix=$(realpath ../build/verilator) && \
    make -j$(nproc) && \
    make install
RUN rm -rf verilator build/verilator/bin/verilator_bin_dbg

# ██╗    ██╗ █████╗ ██╗   ██╗███████╗██╗     ███████╗████████╗
# ██║    ██║██╔══██╗██║   ██║██╔════╝██║     ██╔════╝╚══██╔══╝
# ██║ █╗ ██║███████║██║   ██║█████╗  ██║     █████╗     ██║
# ██║███╗██║██╔══██║╚██╗ ██╔╝██╔══╝  ██║     ██╔══╝     ██║
# ╚███╔███╔╝██║  ██║ ╚████╔╝ ███████╗███████╗███████╗   ██║
#  ╚══╝╚══╝ ╚═╝  ╚═╝  ╚═══╝  ╚══════╝╚══════╝╚══════╝   ╚═╝
FROM build-base AS build-wavelet
WORKDIR /wavelet
COPY .cargo .cargo
COPY wavelet wavelet
COPY wavelet-core wavelet-core
COPY wavelet-elab wavelet-elab
COPY Cargo.toml Cargo.toml
COPY Cargo.lock Cargo.lock
COPY rust-toolchain.toml rust-toolchain.toml
RUN cargo build --release
RUN rm -rf wavelet-core/lean/.lake && \
    mv target/release/wavelet wavelet-bin && \
    rm -rf target && \
    mkdir -p target/release && \
    mv wavelet-bin target/release/wavelet

# ██████╗ ██╗   ██╗███╗   ██╗████████╗██╗███╗   ███╗███████╗
# ██╔══██╗██║   ██║████╗  ██║╚══██╔══╝██║████╗ ████║██╔════╝
# ██████╔╝██║   ██║██╔██╗ ██║   ██║   ██║██╔████╔██║█████╗
# ██╔══██╗██║   ██║██║╚██╗██║   ██║   ██║██║╚██╔╝██║██╔══╝
# ██║  ██║╚██████╔╝██║ ╚████║   ██║   ██║██║ ╚═╝ ██║███████╗
# ╚═╝  ╚═╝ ╚═════╝ ╚═╝  ╚═══╝   ╚═╝   ╚═╝╚═╝     ╚═╝╚══════╝
FROM ubuntu:24.04 AS runtime

# Install runtime dependencies
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        git curl lld unzip make build-essential libtcl \
        python3 python3-pip python3-dev \
        libboost-program-options1.83.0 \
        libboost-thread1.83.0 && \
    rm -rf /var/lib/apt/lists/*

COPY integration-tests/requirements.txt /tmp/requirements.txt
RUN pip3 install --no-cache-dir --break-system-packages -r /tmp/requirements.txt && \
    rm /tmp/requirements.txt

RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --default-toolchain none
RUN curl -fsSL https://code-server.dev/install.sh | sh -s -- --version 4.109.5

# Install cvc5-1.3.3
RUN if [ "$(uname -m)" = "aarch64" ]; then arch=arm64; \
    else arch=x86_64; fi && \
    curl -fsSL -o /tmp/cvc5.zip "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.3/cvc5-Linux-$arch-static.zip" && \
    unzip /tmp/cvc5.zip -d /tmp && \
    mv /tmp/cvc5-Linux-*-static/bin/cvc5 /usr/local/bin && \
    rm -r /tmp/cvc5.zip /tmp/cvc5-Linux-*-static

# Configure code-server
RUN code-server --install-extension leanprover.lean4 && \
    code-server --install-extension rust-lang.rust-analyzer

# Clean up code-server install
RUN rm -rf /root/.cache && \
    find /usr/lib/code-server -name '*.js.map' -delete

# Pull builds from previous stages
COPY --from=build-circt /wavelet/ /wavelet/
COPY --from=build-polygeist /wavelet/ /wavelet/
COPY --from=build-nextpnr /wavelet/ /wavelet/
COPY --from=build-sv2v /wavelet/ /wavelet/
COPY --from=build-yosys /wavelet/ /wavelet/
COPY --from=build-verilator /wavelet/ /wavelet/
COPY --from=build-wavelet /wavelet/ /wavelet/
RUN cp -a /wavelet/integration-tests/build/sv2v/. /usr/local/ && \
    cp -a /wavelet/integration-tests/build/yosys/. /usr/local/ && \
    cp -a /wavelet/integration-tests/build/verilator/. /usr/local/ && \
    rm -rf \
        /wavelet/integration-tests/build/sv2v \
        /wavelet/integration-tests/build/yosys \
        /wavelet/integration-tests/build/verilator

# Documentation and UX
COPY <<EOF /root/.local/share/code-server/User/settings.json
{
    "chat.disableAIFeatures": true,
    "workbench.colorTheme": "Default Light Modern",
    "workbench.startupEditor": "readme",
    "security.workspace.trust.enabled": false,
    "workbench.secondarySideBar.defaultVisibility": "hidden",
    "task.allowAutomaticTasks": "on"
}
EOF
COPY <<EOF /wavelet/.vscode/tasks.json
{
    "version": "2.0.0",
    "tasks": [
        {
            "label": "Open Panel",
            "type": "shell",
            "command": "\${command:workbench.action.togglePanel}",
            "problemMatcher": [],
            "runOptions": { "runOn": "folderOpen" }
        },
        {
            "label": "Install Rust Toolchain",
            "type": "shell",
            "command": "rustup toolchain install",
            "runOptions": { "runOn": "folderOpen" },
            "presentation": {
                "reveal": "silent",
                "panel": "dedicated",
                "close": true
            },
            "isBackground": true
        },
        {
            "label": "Install Lean Toolchain",
            "type": "shell",
            "command": "elan toolchain install \\"\$(cat lean-toolchain)\\" || true",
            "options": { "cwd": "\${workspaceFolder}/wavelet-core/lean" },
            "runOptions": { "runOn": "folderOpen" },
            "presentation": {
                "reveal": "silent",
                "panel": "dedicated",
                "close": true
            },
            "isBackground": true
        }
    ]
}
EOF

RUN echo "PS1='\\w \\\$ '" > /root/.bashrc
COPY <<EOF2 /usr/local/bin/entry.sh
#!/bin/bash

# Check ANSI support
if [[ -t 1 ]] && tput setaf 1 >/dev/null 2>&1 && [[ -z "\${NO_COLOR-}" ]]; then
    bold=\$(tput bold)
    italic=\$(tput sitm)
    underline=\$(tput smul)
    reset=\$(tput sgr0)
    green=\$(tput setaf 2)
else
    bold=
    italic=
    underline=
    reset=
    green=
fi

if [ "\$1" == "server" ]; then
    cat <<EOF

Please visit \${underline}\${bold}http://localhost:8080\${reset} to access the in-browser editor.

If you can't access it, make sure that you have started the container with \${bold}-p 127.0.0.1:8080:8080\${reset}.

EOF
    exec code-server --bind-addr 0.0.0.0:8080 --auth none "\${@:2}" /wavelet
else
    cat <<EOF

Welcome to the artifact accompanying the paper:

    \${bold}Let it Flow: A Formally Verified Compilation Framework for Asynchronous Dataflow\${reset}

To run some quick sanity checks:

    \\\$ make -C integration-tests sanity-check \${reset}

You can also exit and restart this image as a VS code server for a better experience:

    \\\$ docker run -p 127.0.0.1:8080:8080 wavelet-artifact server

Then visit \${underline}\${bold}http://localhost:8080\${reset} to access the in-browser editor.

EOF
    exec "\${@:-/bin/bash}"
fi
EOF2
RUN chmod +x /usr/local/bin/entry.sh

# Add rest of the required files
COPY integration-tests/sim /wavelet/integration-tests/sim
COPY integration-tests/tests /wavelet/integration-tests/tests
COPY integration-tests/Makefile /wavelet/integration-tests/Makefile
COPY README.md /wavelet/README.md

# ███████╗██╗███╗   ██╗ █████╗ ██╗
# ██╔════╝██║████╗  ██║██╔══██╗██║
# █████╗  ██║██╔██╗ ██║███████║██║
# ██╔══╝  ██║██║╚██╗██║██╔══██║██║
# ██║     ██║██║ ╚████║██║  ██║███████╗
# ╚═╝     ╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝
FROM scratch AS final
COPY --from=runtime / /
WORKDIR /wavelet
ENV PATH="/root/.elan/bin:/root/.cargo/bin:${PATH}"
ENTRYPOINT ["/usr/local/bin/entry.sh"]
