#!/bin/sh
#
# Compiling C to Verilog through Polygeist + CIRCT.
# 
# Notes:
# 1. All arguments are passed to `cgeist`.
# 2. The source code must contain exactly one function.
# 3. The function parameters must only contain statically-sized arrays and scalars (no pointers);
#    although the array sizes are not actually used in the output Handshake IR or Verilog.
# 4. No pointer arithmetic is allowed.

set -eu

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cgeist="$script_dir/../build/polygeist/bin/cgeist"
hlstool="$script_dir/../build/circt/bin/hlstool"

if ! [ -e "$cgeist" ]; then
    echo "cgeist binary not found at $cgeist; see Makefile for how to build it"
    exit 1
fi

if ! [ -e "$hlstool" ]; then
    echo "hlstool binary not found at $hlstool; see Makefile for how to build it"
    exit 1
fi

"$cgeist" -O3 --memref-fullrank -S "$@" | \
    sed -E 's/[[:space:]]*attributes[[:space:]]*\{[^}]*\}//g' | \
    build/circt/bin/hlstool \
        --verilog \
        --dynamic-hw \
        --buffering-strategy=all \
        --lowering-options=disallowLocalVariables \
        --verify-each
