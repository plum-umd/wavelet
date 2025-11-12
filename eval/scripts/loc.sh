#!/bin/bash

set -euo pipefail

CLOC_OPTS="--quiet --sum-one"

cd "$(dirname "$0")/../../lean"

echo "============ CFC code ============"
cloc $CLOC_OPTS Wavelet/Compile/Fn/Defs.lean

echo "============ CFC proof ============"
cloc $CLOC_OPTS Wavelet/Seq/VarMap.lean \
    Wavelet/Seq/Fn.lean \
    Wavelet/Seq/AffineVar.lean \
    Wavelet/Dataflow/AffineChan.lean \
    Wavelet/Dataflow/Proc.lean \
    Wavelet/Dataflow/Abbrev.lean \
    Wavelet/Dataflow/AsyncOp.lean \
    Wavelet/Dataflow/ChanMap.lean \
    Wavelet/Compile/Fn/Lemmas.lean \
    Wavelet/Compile/Fn/Simulation.lean \
    Wavelet/Compile/Fn/Simulation/BrMerges.lean \
    Wavelet/Compile/Fn/Simulation/Ret.lean \
    Wavelet/Compile/Fn/Simulation/Br.lean \
    Wavelet/Compile/Fn/Simulation/Op.lean \
    Wavelet/Compile/Fn/Simulation/Init.lean \
    Wavelet/Compile/Fn/Simulation/Invariants.lean \
    Wavelet/Compile/Fn/Simulation/Tail.lean

echo "============ Linking code ============"
cloc $CLOC_OPTS Wavelet/Compile/Prog/Defs.lean \
    Wavelet/Compile/MapChans.lean

echo "============ Linking proof ============"
cloc $CLOC_OPTS Wavelet/Seq/Prog.lean \
    Wavelet/Semantics/Link.lean \
    Wavelet/Compile/AffineOp.lean \
    Wavelet/Compile/Prog/Simulation.lean

echo "============ Determinacy proof ============"
cloc $CLOC_OPTS Wavelet/Determinacy/PCM.lean \
    Wavelet/Determinacy/OpSpec.lean \
    Wavelet/Semantics/Confluence.lean \
    Wavelet/Semantics/Guard.lean \
    Wavelet/Dataflow/IndexedStep.lean \
    Wavelet/Dataflow/EqMod.lean \
    Wavelet/Seq/Typed.lean \
    Wavelet/Determinacy/DisjointTokens.lean \
    Wavelet/Determinacy/Confluence.lean \
    Wavelet/Determinacy/Hetero.lean \
    Wavelet/Determinacy/Congr.lean \
    Wavelet/Determinacy/MapTokens.lean \
    Wavelet/Determinacy/Determinism.lean \
    Wavelet/Determinacy/Defs.lean \
    Wavelet/Determinacy/Convert.lean \
    Wavelet/HighLevel.lean

echo "============ Optimization code ============"
cloc $CLOC_OPTS Wavelet/Compile/Rewrite/Rename.lean \
    Wavelet/Compile/Rewrite/EraseGhost.lean \
    Wavelet/Compile/Rewrite/Defs.lean

echo "============ Common utils ============"
cloc $CLOC_OPTS Wavelet/Data/List.lean \
    Wavelet/Data/Except.lean \
    Wavelet/Data/Vector.lean \
    Wavelet/Semantics/Defs.lean \
    Wavelet/Semantics/Lts.lean \
    Wavelet/Semantics/OpInterp.lean \
    Wavelet/Seq/Properties.lean

echo "============ Seq semantics (duplicating!) ============"
cloc $CLOC_OPTS Attempts/SeqSpec.lean

echo "============ Proc semantics (duplicating!) ============"
cloc $CLOC_OPTS Attempts/DataflowSpec.lean

cd "../dfx"

echo "============ Type checker + perm validator ==========="
cloc src

echo "============ Perm validator ==========="
cloc src/ghost/checker
