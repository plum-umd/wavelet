"""
Collects stats from compilation results and generates LaTeX tables
comparing Wavelet, Wavelet without optimizations, RipTide (CGRA),
and CIRCT (HLS).
"""

from __future__ import annotations

import re
import json

from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np

def configure_mpl(use_tex: bool = True):
    if use_tex:
        mpl.rcParams.update({
            "text.usetex": True,
            "text.latex.preamble": r"\usepackage{libertine}\usepackage[libertine]{newtxmath}\usepackage{inconsolata}",
            "font.family": "serif",
            "font.size": 14,
        })
    else:
        mpl.rcParams.update({
            "text.usetex": False,
            "font.size": 14,
        })

BENCH_NAMES = [
    "nn_vadd", "nn_norm", "nn_relu", "nn_pool",
    "nn_fc", "nn_conv", "dmv", "dmm", "dither", "sort",
]

TRIVIAL_OPS = { "fork", "forward", "const", "sink", "inact" } 
CF_OPS = { "switch", "steer", "merge", "carry", "order", "forwardc", "inv" }
MEM_OPS = { "load", "store" }

def test_path(name: str, suffix: str) -> Path:
    return Path(__file__).parent.parent / "tests" / name.replace("_", "-") / f"test.{suffix}"

def read_file(path: Path) -> str | None:
    try:
        return path.read_text()
    except FileNotFoundError:
        return None

def load_json(path: Path) -> dict | None:
    text = read_file(path)
    return json.loads(text) if text is not None else None

def parse_total_cycles(path: Path) -> int | None:
    """From wavelet-sim / riptide-sim logs: 'total cycles: N'"""
    text = read_file(path)
    if text is None:
        return None
    m = re.search(r"total cycles:\s*(\d+)", text)
    return int(m.group(1)) if m else None

def has_memory_mismatch(path: Path) -> bool:
    """Check if a simulation log contains 'memory mismatch' warnings."""
    text = read_file(path)
    return text is not None and "memory mismatch" in text

def parse_rtl_cycles(path: Path) -> int | None:
    """Assuming simulation clock period is 1 ns."""
    text = read_file(path)
    if text is None:
        return None
    # Match the summary TESTS= line's SIM_TIME field
    m = re.search(r"SKIP=\d+\s+([0-9.]+)", text)
    return int(float(m.group(1))) if m else None

def graph_size(stats: tuple[int, int, int] | None) -> int | None:
    """Total non-trivial ops from a (cf, sync, mem) tuple."""
    return sum(stats) if stats else None

def parse_graph_size_riptide(path: Path) -> int | None:
    """Vertex count from riptide JSON."""
    data = load_json(path)
    return len(data["vertices"]) if data else None

def wavelet_op_name(op) -> str:
    """Extract canonical op name from a wavelet atom's 'op' field."""
    if isinstance(op, str):
        return op
    keys = list(op.keys())
    assert len(keys) == 1, f"unexpected op format {op}"
    # merge with popLeft state is a carry (loop-carried value)
    if keys[0] == "merge" and op["merge"]["state"] == "popLeft":
        return "carry"
    return keys[0]

def parse_wavelet_cf_stats(path: Path) -> tuple[int, int, int] | None:
    """Parses and categorizes Wavelet operators in the given dataflow graph."""
    data = load_json(path)
    if data is None:
        return None
    cf = sync = mem = 0
    for atom in data["atoms"]:
        inner = atom.get("async") or atom.get("op")
        name = wavelet_op_name(inner["op"])
        if name in TRIVIAL_OPS:
            continue
        if name in CF_OPS:
            cf += 1
        elif name in MEM_OPS:
            mem += 1
        else:
            sync += 1
    return cf, sync, mem

def riptide_op_type(op_name: str) -> str:
    """Classify riptide op by its name prefix."""
    if op_name.startswith("ARITH_") or op_name.startswith("MUL_"):
        return "sync"
    if op_name.startswith("MEM_"):
        return "mem"
    if op_name.startswith("CF_") or op_name.startswith("STREAM_"):
        return "cf"
    assert False, f"unknown riptide op: {op_name}"

def parse_riptide_cf_stats(path: Path) -> tuple[int, int, int] | None:
    data = load_json(path)
    if data is None:
        return None
    cf = sync = mem = 0
    for v in data["vertices"]:
        kind = riptide_op_type(v["op"])
        if kind == "cf":
            cf += 1
        elif kind == "mem":
            mem += 1
        else:
            sync += 1
    return cf, sync, mem

def parse_nextpnr(path: Path) -> dict | None:
    """Extract LUTs, FFs, and max frequency from nextpnr place-and-route log."""
    text = read_file(path)
    if text is None:
        return None
    luts_m = re.search(r"Total LUT4s:\s+(\d+)/", text)
    ffs_m = re.search(r"Total DFFs:\s+(\d+)/", text)
    # Last "Max frequency" line is the post-routing result
    freq_ms = list(re.finditer(r"Max frequency for clock.*?:\s+([0-9.]+)\s+MHz", text))
    luts = int(luts_m.group(1)) if luts_m else None
    ffs = int(ffs_m.group(1)) if ffs_m else None
    freq_mhz = float(freq_ms[-1].group(1)) if freq_ms else None
    # One match = post-placement only (post-routing not yet available)
    freq_post_placement = len(freq_ms) == 1
    return {"luts": luts, "ffs": ffs, "freq_mhz": freq_mhz, "freq_post_placement": freq_post_placement}

def parse_compiler_perf(path: Path) -> dict[str, float] | None:
    """Parse compiler phase timings from a .wavelet.json.log file."""
    text = read_file(path)
    if text is None:
        return None
    phases = {
        "type checking + elaboration": "tc",
        "validating token placement": "tv",
        "lowering control-flow": "cfc",
        "optimization": "opt",
    }
    result = {}
    for phase_label, key in phases.items():
        m = re.search(rf"\[{re.escape(phase_label)}\] finished in (\d+) ms", text)
        if m:
            result[key] = int(m.group(1)) / 1000.0
    return result if len(result) == len(phases) else None


def cf_pct_str(stats: tuple[int, int, int] | None) -> str | None:
    """Format CF ops as 'N (X%)' where X is percentage of non-trivial ops."""
    if stats is None:
        return None
    cf, sync, mem = stats
    total = cf + sync + mem
    pct = round(100 * cf / total) if total else 0
    return rf"{pct}"

def collect_cgra(name: str) -> dict:
    """Collect all CGRA table columns for one benchmark."""
    # Steps: total cycles from high-level dataflow simulation
    steps_wv = parse_total_cycles(test_path(name, "wavelet-sim.log"))
    steps_wv_noopt = parse_total_cycles(test_path(name, "wavelet-noopt-sim.log"))
    steps_rp = parse_total_cycles(test_path(name, "riptide-sim.log"))
    steps_rp_noopt = parse_total_cycles(test_path(name, "riptide-sim.nostream.log"))

    # Op stats from dataflow graph JSON: (cf, sync, mem) counts
    wv_cf = parse_wavelet_cf_stats(test_path(name, "wavelet.json"))
    wv_noopt_cf = parse_wavelet_cf_stats(test_path(name, "wavelet-noopt.json"))
    rp_cf = parse_riptide_cf_stats(test_path(name, "riptide.json"))
    rp_noopt_cf = parse_riptide_cf_stats(test_path(name, "riptide.nostream.json"))

    # Graph sizes: non-trivial ops (wavelet), vertex count (riptide)
    gs_rp = parse_graph_size_riptide(test_path(name, "riptide.json"))
    gs_rp_noopt = parse_graph_size_riptide(test_path(name, "riptide.nostream.json"))

    # Memory mismatch errors in simulation logs
    err_rp = has_memory_mismatch(test_path(name, "riptide-sim.log"))
    err_rp_noopt = has_memory_mismatch(test_path(name, "riptide-sim.nostream.log"))

    return {
        "steps": { "wv": steps_wv, "wv_noopt": steps_wv_noopt, "rp": steps_rp, "rp_noopt": steps_rp_noopt },
        "graph_size": { "wv": graph_size(wv_cf), "wv_noopt": graph_size(wv_noopt_cf), "rp": gs_rp, "rp_noopt": gs_rp_noopt },
        "cf_pct": {
            "wv": cf_pct_str(wv_cf),
            "wv_noopt": cf_pct_str(wv_noopt_cf),
            "rp": cf_pct_str(rp_cf),
            "rp_noopt": cf_pct_str(rp_noopt_cf),
        },
        "errors": { "rp": err_rp, "rp_noopt": err_rp_noopt },
    }

def collect_hls(name: str) -> dict:
    """Collect all HLS table columns for one benchmark."""
    # Cycles: total SIM_TIME from cocotb RTL simulation logs
    cyc_wv = parse_rtl_cycles(test_path(name, "wavelet.log"))
    cyc_wv_noopt = parse_rtl_cycles(test_path(name, "wavelet-noopt.log"))
    cyc_crt = parse_rtl_cycles(test_path(name, "circt.log"))

    # LUTs, FFs, frequency from nextpnr place-and-route logs
    pnr_wv = parse_nextpnr(test_path(name, "wavelet.nextpnr.json.log"))
    pnr_wv_noopt = parse_nextpnr(test_path(name, "wavelet-noopt.nextpnr.json.log"))
    pnr_crt = parse_nextpnr(test_path(name, "circt.nextpnr.json.log"))

    def get(d: dict | None, key: str):
        return d[key] if d else None

    # Execution time (us) = cycles * (1000 / freq_mhz) / 1000
    def exec_time(cyc, pnr):
        if cyc is None or pnr is None or pnr["freq_mhz"] is None:
            return None
        return round(cyc / pnr["freq_mhz"], 1)

    def is_post_placement(pnr):
        return pnr is not None and pnr.get("freq_post_placement", False)

    return {
        "cycles": { "wv": cyc_wv, "wv_noopt": cyc_wv_noopt, "crt": cyc_crt },
        "exec_time": {
            "wv": exec_time(cyc_wv, pnr_wv),
            "wv_noopt": exec_time(cyc_wv_noopt, pnr_wv_noopt),
            "crt": exec_time(cyc_crt, pnr_crt),
        },
        "freq_post_placement": {
            "wv": is_post_placement(pnr_wv),
            "wv_noopt": is_post_placement(pnr_wv_noopt),
            "crt": is_post_placement(pnr_crt),
        },
        "luts": {
            "wv": get(pnr_wv, "luts"),
            "wv_noopt": get(pnr_wv_noopt, "luts"),
            "crt": get(pnr_crt, "luts"),
        },
        "ffs": {
            "wv": get(pnr_wv, "ffs"),
            "wv_noopt": get(pnr_wv_noopt, "ffs"),
            "crt": get(pnr_crt, "ffs"),
        },
    }

def to_cell(val, decimals: int = 2) -> str:
    if val is None:
        return "--"
    if isinstance(val, float):
        return f"{val:.{decimals}f}"
    return str(val)

def tt_name(name: str) -> str:
    short = name.removeprefix("nn_")
    return f"\\texttt{{{short.replace('_', chr(92) + 'textunderscore{}')}}}"

def emit_table(
    all_stats: dict[str, dict],
    # (header, dict key, decimal places)
    metrics: list[tuple[str, str, int]],
    # (display label, dict key in inner dicts)
    compilers: list[tuple[str, str]],
    errors_key: str | None = None,
    error_metrics: set[str] | None = None,
    # dict key whose bool values trigger a dagger on specified metrics
    dagger_key: str | None = None,
    dagger_metrics: set[str] | None = None,
) -> str:
    nc = len(compilers)
    col_spec = "l" + (f"|{'r' * nc}") * len(metrics)
    lines = [rf"\begin{{tabular}}{{{col_spec}}}"]

    # Multicolumn header
    mc_parts = []
    for i, (header, _, _) in enumerate(metrics):
        sep = "c|" if i < len(metrics) - 1 else "c"
        mc_parts.append(rf" & \multicolumn{{{nc}}}{{{sep}}}{{{header}}}")
    lines.append("".join(mc_parts) + r" \\")

    # Compiler labels row
    compiler_labels = "".join(f" & {lbl}" for lbl, _ in compilers) * len(metrics)
    lines.append("Test" + compiler_labels + r" \\")
    lines.append(r"\hline")

    # Data rows
    for name in BENCH_NAMES:
        stats = all_stats[name]
        errors = stats.get(errors_key, {}) if errors_key else {}
        daggers = stats.get(dagger_key, {}) if dagger_key else {}
        cells = [tt_name(name)]
        for _, metric_key, decimals in metrics:
            metric = stats[metric_key]
            for _, comp_key in compilers:
                cell = to_cell(metric[comp_key], decimals)
                if errors.get(comp_key) and (error_metrics is None or metric_key in error_metrics):
                    cell = cell + r"$^\times$"
                if daggers.get(comp_key) and (dagger_metrics is None or metric_key in dagger_metrics) and cell != "--":
                    cell = cell + r"$^\dagger$"
                cells.append(cell)
        lines.append(" & ".join(cells) + r" \\")

    lines.append(r"\end{tabular}")
    return "\n".join(lines)

def generate_cgra_table(all_stats: dict[str, dict]) -> str:
    return emit_table(
        all_stats,
        metrics=[
            ("Steps",       "steps",      0),
            ("Graph Sizes", "graph_size", 0),
            (r"\%CF Ops",   "cf_pct",     0),
        ],
        compilers=[
            (r"\textbf{Wv}",     "wv"),
            (r"\textbf{Wv}$^*$", "wv_noopt"),
            ("RP",               "rp"),
            ("RP$^*$",           "rp_noopt"),
        ],
        errors_key="errors",
        error_metrics={"steps"},
    )

def generate_hls_table(all_stats: dict[str, dict]) -> str:
    return emit_table(
        all_stats,
        metrics=[
            ("Cycles",                         "cycles",    0),
            (r"Exec.\ Time ($\mu$s)", "exec_time", 1),
            ("LUTs",                           "luts",      0),
            ("FFs",                            "ffs",       0),
        ],
        compilers=[
            (r"\textbf{Wv}",     "wv"),
            (r"\textbf{Wv}$^*$", "wv_noopt"),
            ("CRT",              "crt"),
        ],
        dagger_key="freq_post_placement",
        dagger_metrics={"exec_time"},
    )

def is_comment(line: str, ext: str) -> bool:
    """Check if a line is a comment (single-line // or C-style /* ... */)."""
    s = line.strip()
    if s.startswith("//"):
        return True
    if ext == "lean" and (s.startswith("--") or s.startswith("/-") or s.startswith("-/") or s.endswith("-/")):
        return True
    if ext == "c" and (s.startswith("/*") or s.startswith("*") or s.endswith("*/")):
        return True
    return False

def count_lines(path: Path) -> int | None:
    """Count non-empty, non-comment lines in a file."""
    text = read_file(path)
    if text is None:
        return None
    ext = path.suffix.lstrip(".")
    return sum(1 for line in text.splitlines()
               if line.strip() and not is_comment(line, ext))

def count_annotations(path: Path) -> int | None:
    """Count annotation lines: #[cap...] attributes and fence!() calls."""
    text = read_file(path)
    if text is None:
        return None
    count = 0
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#[cap"):
            count += 1
        elif "fence!()" in stripped:
            count += 1
    return count

def collect_compiler_perf(name: str) -> dict[str, float | None]:
    """Collect compiler phase timings and source LoC for one benchmark."""
    perf = parse_compiler_perf(test_path(name, "wavelet.json.log"))
    if perf is None:
        result = {"tc": None, "tv": None, "opt": None, "total": None}
    else:
        perf["total"] = round(perf["tc"] + perf["tv"] + perf["cfc"] + perf["opt"], 2)
        del perf["cfc"]
        result = perf
    result["loc_c"] = count_lines(test_path(name, "c"))
    result["loc_dsl"] = count_lines(test_path(name, "rs"))
    result["loc_ann"] = count_annotations(test_path(name, "rs"))
    return result

def generate_compiler_perf_table(all_stats: dict[str, dict]) -> str:
    loc_cols = [("C", "loc_c"), ("DSL", "loc_dsl"), ("Ann", "loc_ann")]
    time_cols = [("TC", "tc"), ("TV", "tv"), ("Opt", "opt"), ("Total", "total")]
    lines = [r"\begin{tabular}{l|rrr|rrrr}"]
    lines.append(
        r"& \multicolumn{3}{c|}{Source LoC}"
        r" & \multicolumn{4}{c}{Compiler Time (s)} \\"
    )
    loc_hdrs = " & ".join(h for h, _ in loc_cols)
    time_hdrs = " & ".join(h for h, _ in time_cols)
    lines.append(f"Test & {loc_hdrs} & {time_hdrs}" + r" \\")
    lines.append(r"\hline")
    for name in BENCH_NAMES:
        stats = all_stats[name]
        cells = [tt_name(name)]
        for _, key in loc_cols:
            cells.append(to_cell(stats[key], 0))
        for _, key in time_cols:
            cells.append(to_cell(stats[key]))
        lines.append(" & ".join(cells) + r" \\")
    lines.append(r"\end{tabular}")
    return "\n".join(lines)

def geomean(values: list[float]) -> float:
    """Geometric mean of a list of positive floats."""
    from math import prod, pow
    return pow(prod(values), 1.0 / len(values))

def geomean_ratio(all_stats: dict, metric: str, num_key: str, den_key: str) -> float | None:
    """Geometric mean of num/den ratios across benchmarks, skipping None."""
    ratios = []
    for name in BENCH_NAMES:
        m = all_stats[name][metric]
        n, d = m.get(num_key), m.get(den_key)
        if n is not None and d is not None and d != 0:
            ratios.append(n / d)
    return round(geomean(ratios), 2) if ratios else None

def emit_stats(cgra: dict, hls: dict, perf: dict) -> str:
    defs = [
        ("WvStepsOverRP",          "steps",     "wv",       "rp"),
        ("WvNooptStepsOverRP",     "steps",     "wv_noopt", "rp"),
        ("WvStepsOverRPNoopt",     "steps",     "wv",       "rp_noopt"),
        ("WvNooptStepsOverRPNoopt","steps",     "wv_noopt", "rp_noopt"),
        ("WvGSOverRP",             "graph_size","wv",       "rp"),
        ("WvNooptGSOverRP",        "graph_size","wv_noopt", "rp"),
        ("WvGSOverRPNoopt",        "graph_size","wv",       "rp_noopt"),
        ("WvNooptGSOverRPNoopt",   "graph_size","wv_noopt", "rp_noopt"),
    ]
    hls_defs = [
        ("WvCycOverCRT",       "cycles",    "wv",       "crt"),
        ("WvNooptCycOverCRT",  "cycles",    "wv_noopt", "crt"),
        ("WvExecOverCRT",      "exec_time", "wv",       "crt"),
        ("WvNooptExecOverCRT", "exec_time", "wv_noopt", "crt"),
        ("WvLUTsOverCRT",      "luts",      "wv",       "crt"),
        ("WvNooptLUTsOverCRT", "luts",      "wv_noopt", "crt"),
        ("WvFFsOverCRT",       "ffs",       "wv",       "crt"),
        ("WvNooptFFsOverCRT",  "ffs",       "wv_noopt", "crt"),
    ]
    lines = []
    for var, metric, num, den in defs:
        val = geomean_ratio(cgra, metric, num, den)
        lines.append(rf"\newcommand{{\{var}}}{{{val}}}")
    for var, metric, num, den in hls_defs:
        val = geomean_ratio(hls, metric, num, den)
        lines.append(rf"\newcommand{{\{var}}}{{{val}}}")
    # DSL LoC / C LoC geometric mean
    ratios = []
    for name in BENCH_NAMES:
        dsl = perf[name]["loc_dsl"]
        c = perf[name]["loc_c"]
        if dsl is not None and c is not None and c != 0:
            ratios.append(dsl / c)
    if ratios:
        val = round(geomean(ratios), 2)
        lines.append(rf"\newcommand{{\DSLOverC}}{{{val}}}")
    # Simulation proof ratio: proof LoC / (code + spec) LoC for CFC and Linking
    project_root = Path(__file__).parent.parent.parent
    lean_base = project_root / "wavelet-core" / "lean" / "Wavelet"
    sim_components = [
        (CF_CONVERSION_CODE, lean_base, CF_CONVERSION_SPEC, CF_CONVERSION_PROOF),
        (LINKING_CODE,       lean_base, LINKING_SPEC,       LINKING_PROOF),
    ]
    sim_code_spec = 0
    sim_proof = 0
    for code_files, code_base, spec_files, proof_files in sim_components:
        sim_code_spec += count_files(code_base, code_files) + count_files(lean_base, spec_files)
        sim_proof += count_files(lean_base, proof_files)
    if sim_code_spec > 0:
        val = round(sim_proof / sim_code_spec, 1)
        lines.append(rf"\newcommand{{\simProofRatio}}{{{val}}}")
    # Total Rust LoC
    rust_base = project_root / "wavelet-elab" / "src"
    rust_loc = count_files(rust_base, TYPE_CHECKER_CODE + PERM_VALIDATOR_CODE)
    lines.append(rf"\newcommand{{\rustLoc}}{{{fmt_loc(rust_loc)}\xspace}}")
    # Total Lean LoC by category (code, spec, proof) across all components
    all_lean_code_files = [
        (CF_CONVERSION_CODE, lean_base),
        (LINKING_CODE,       lean_base),
    ]
    all_lean_spec_files = CF_CONVERSION_SPEC + LINKING_SPEC + DETERMINACY_SPEC
    all_lean_proof_files = CF_CONVERSION_PROOF + LINKING_PROOF + DETERMINACY_PROOF
    lean_code_loc = sum(count_files(base, files) for files, base in all_lean_code_files)
    lean_spec_loc = count_files(lean_base, all_lean_spec_files)
    lean_proof_loc = count_files(lean_base, all_lean_proof_files)
    lines.append(rf"\newcommand{{\leanCodeLoc}}{{{fmt_loc(lean_code_loc)}\xspace}}")
    lines.append(rf"\newcommand{{\leanSpecLoc}}{{{fmt_loc(lean_spec_loc)}\xspace}}")
    lines.append(rf"\newcommand{{\leanProofLoc}}{{{fmt_loc(lean_proof_loc)}\xspace}}")
    cfc_proof_loc = count_files(lean_base, CF_CONVERSION_PROOF)
    det_proof_loc = count_files(lean_base, DETERMINACY_PROOF)
    lines.append(rf"\newcommand{{\cfcProofLoc}}{{{fmt_loc(cfc_proof_loc)}\xspace}}")
    lines.append(rf"\newcommand{{\detProofLoc}}{{{fmt_loc(det_proof_loc)}\xspace}}")
    lean_code_spec = lean_code_loc + lean_spec_loc
    if lean_code_spec > 0:
        val = round(lean_proof_loc / lean_code_spec, 1)
        lines.append(rf"\newcommand{{\leanProofRatio}}{{{val}}}")
    # Geometric mean of %CF for each compiler
    for var, key in [("WvCFPct", "wv"), ("WvNooptCFPct", "wv_noopt"),
                     ("RPCFPct", "rp"), ("RPNooptCFPct", "rp_noopt")]:
        pcts = []
        for name in BENCH_NAMES:
            v = cgra[name]["cf_pct"].get(key)
            if v is not None:
                pcts.append(float(v))
        if pcts:
            val = round(geomean(pcts))
            lines.append(rf"\newcommand{{\{var}}}{{{val}}}")
    return "\n".join(lines)

TYPE_CHECKER_CODE = [
    "lib.rs", "main.rs", "ir.rs", "check.rs", "error.rs", "env.rs", "parse.rs",
    "logic/mod.rs", "logic/cap.rs", "logic/region.rs",
    "logic/semantic/mod.rs", "logic/semantic/solver.rs", "logic/semantic/region_set.rs",
    "logic/syntactic/mod.rs", "logic/syntactic/solver.rs",
    "ghost/mod.rs", "ghost/ir.rs", "ghost/affine.rs",
    "ghost/fracperms/mod.rs", "ghost/fracperms/expr.rs",
    "ghost/fracperms/normalize.rs", "ghost/fracperms/solver.rs",
    "ghost/json.rs", "ghost/lower.rs",
]

PERM_VALIDATOR_CODE = [
    "ghost/checker/mod.rs", "ghost/checker/context.rs", "ghost/checker/perm_env.rs",
    "ghost/checker/permission.rs", "ghost/checker/pretty_print.rs",
    "ghost/checker/contract.rs", "ghost/checker/synthesis.rs",
    "ghost/checker/program_checker.rs", "ghost/checker/trace.rs",
    "ghost/checker/utils.rs", "ghost/checker/validation.rs",
    "ghost/checker/tests.rs",
]

CF_CONVERSION_CODE = [
    "Compile/Fn.lean",
    "Seq/Fn.lean", "Dataflow/Proc.lean", "Dataflow/AsyncOp.lean",
]
CF_CONVERSION_SPEC = [
    "Semantics/Defs.lean", "Semantics/OpInterp.lean",
    "Seq/AffineVar.lean", "Seq/VarMap.lean",
    "Dataflow/AffineChan.lean",
    "Dataflow/ChanMap.lean",
    "Data/Basic.lean",
]
CF_CONVERSION_PROOF = [
    "Thm/Compile/Fn/AffineVar.lean", "Thm/Compile/Fn/Lemmas.lean",
    "Thm/Compile/Fn/Simulation.lean",
    "Thm/Compile/Fn/Simulation/Br.lean", "Thm/Compile/Fn/Simulation/BrMerges.lean",
    "Thm/Compile/Fn/Simulation/Init.lean", "Thm/Compile/Fn/Simulation/Invariants.lean",
    "Thm/Compile/Fn/Simulation/Op.lean", "Thm/Compile/Fn/Simulation/Ret.lean",
    "Thm/Compile/Fn/Simulation/Tail.lean",
    "Thm/Seq/AffineVar.lean", "Thm/Seq/VarMap.lean",
    "Thm/Dataflow/AffineChan.lean", "Thm/Dataflow/ChanMap.lean",
    "Thm/Dataflow/AltStep.lean",
    "Thm/Data/Function.lean", "Thm/Data/List.lean", "Thm/Data/Vector.lean",
    "Thm/Semantics/Simulation.lean", "Thm/Seq/Invariants.lean",
]

LINKING_CODE = ["Compile/Prog.lean", "Compile/MapChans.lean", "Seq/Prog.lean"]
LINKING_SPEC = ["Semantics/Link.lean"]
LINKING_PROOF = [
    "Thm/Compile/AffineOp.lean", "Thm/Compile/MapChans.lean", "Thm/Compile/Prog.lean",
    "Thm/Compile/Prog/AffineVar.lean", "Thm/Compile/Prog/Simulation.lean",
    "Thm/Seq/Prog.lean", "Thm/Semantics/Link.lean",
]

DETERMINACY_SPEC = [
    "Determinacy/PCM.lean", "Determinacy/OpSpec.lean", "Semantics/Lts.lean",
]
DETERMINACY_PROOF = [
    "Thm/Determinacy/Confluence.lean", "Thm/Determinacy/Congr.lean",
    "Thm/Determinacy/Convert.lean", "Thm/Determinacy/Defs.lean",
    "Thm/Determinacy/Determinism.lean", "Thm/Determinacy/DisjointTokens.lean",
    "Thm/Determinacy/HasNoTokenConst.lean", "Thm/Determinacy/Hetero.lean",
    "Thm/Determinacy/MapTokens.lean", "Thm/Determinacy/OpSpec.lean",
    "Thm/Determinacy/PCM.lean",
    "Thm/Semantics/Confluence.lean", "Thm/Semantics/Guard.lean",
    "Thm/Semantics/Invariant.lean", "Thm/Semantics/Label.lean",
    "Thm/Semantics/OpInterp.lean",
    "Thm/Dataflow/EqMod.lean", "Thm/Dataflow/IndexedStep.lean",
    "Thm/HighLevel.lean",
]

OPTIMIZATION_CODE = ["Compile/Rewrite.lean", "Compile/EraseGhost.lean"]

def count_files(base_dir: Path, files: list[str]) -> int:
    total = 0
    for f in files:
        n = count_lines(base_dir / f)
        if n is None:
            raise RuntimeError(f"missing file {base_dir / f}")
        total += n
    return total

def fmt_loc(n: int) -> str:
    if n == 0:
        return "-"
    return f"{n:,}"

def generate_loc_table() -> str:
    """Generate LaTeX table estimating lines of code by component."""
    project_root = Path(__file__).parent.parent.parent
    lean_base = project_root / "wavelet-core" / "lean" / "Wavelet"
    rust_base = project_root / "wavelet-elab" / "src"

    # (name, time, code_files, code_base, spec_files, proof_files)
    # TODO: the man-week estimates are hardcoded now, based on the commit history
    components = [
        ("Type Checker",    8,  TYPE_CHECKER_CODE,    rust_base, [],                  []),
        ("Perm. Validator", 4,  PERM_VALIDATOR_CODE,  rust_base, [],                  []),
        ("CF Conversion",   8,  CF_CONVERSION_CODE,   lean_base, CF_CONVERSION_SPEC,  CF_CONVERSION_PROOF),
        ("Linking",         4,  LINKING_CODE,          lean_base, LINKING_SPEC,        LINKING_PROOF),
        ("Determinacy",     8,  [],                    lean_base, DETERMINACY_SPEC,    DETERMINACY_PROOF),
        ("Optimization",    3,  OPTIMIZATION_CODE,     lean_base, [],                  []),
    ]

    lines = [r"\begin{tabular}{l|rrrr}"]
    lines.append(r"    Component & Time & Code & Spec & Proofs \\")
    lines.append(r"    \hline")

    total_time = 0
    total_code = 0
    total_spec = 0
    total_proof = 0

    for name, time, code_files, code_base, spec_files, proof_files in components:
        code_n = count_files(code_base, code_files)
        spec_n = count_files(lean_base, spec_files)
        proof_n = count_files(lean_base, proof_files)

        total_time += time
        total_code += code_n
        total_spec += spec_n
        total_proof += proof_n

        lines.append(
            f"    {name:20s}& {time}   & {fmt_loc(code_n):>7s} & {fmt_loc(spec_n):>7s} & {fmt_loc(proof_n):>7s} \\\\"
        )

    lines.append(r"    \hline")
    lines.append(
        f"    {'Total':20s}& {total_time}  & {fmt_loc(total_code):>7s} & {fmt_loc(total_spec):>7s} & {fmt_loc(total_proof):>7s} \\\\"
    )
    lines.append(r"\end{tabular}")
    return "\n".join(lines)

PLOT_COLORS = {
    "wv":       "#4C72B0",
    "rp":       "#D1D1D1",
    "rp_noopt": "#CCB974",
    "crt":      "#D1D1D1",
}

PLOT_LABELS = {
    "wv": "Wavelet", "rp": "RipTide", "rp_noopt": "RipTide w/o Stream", "crt": "CIRCT",
}

def make_bar_plot(ax, all_stats, metric_key, compiler_keys, baseline_key, title, bench_names=None, x_rotation=0):
    """Plot values relative to baseline_key. All compiler_keys (including baseline) are drawn as bars."""
    if bench_names is None:
        bench_names = BENCH_NAMES
    if mpl.rcParams.get("text.usetex"):
        bench_labels = [rf"\texttt{{{n.removeprefix('nn_').replace('_', r'\_')}}}" for n in bench_names]
    else:
        bench_labels = [n.removeprefix("nn_") for n in bench_names]
    x = np.arange(len(bench_names))
    n_bars = len(compiler_keys)
    width = 0.9 / n_bars

    for i, key in enumerate(compiler_keys):
        vals = []
        for name in bench_names:
            v = all_stats[name][metric_key].get(key)
            base = all_stats[name][metric_key].get(baseline_key)
            if v is not None and base:
                vals.append(v / base)
            else:
                vals.append(0)
        offset = (i - (n_bars - 1) / 2) * width
        ax.bar(x + offset, vals, width, label=PLOT_LABELS[key],
               color=PLOT_COLORS[key], edgecolor="none")

    ax.tick_params(axis="y", labelsize=14)
    ax.set_xticks(x)
    ax.set_xticklabels(bench_labels, rotation=x_rotation,
                       ha="right" if x_rotation else "center", fontsize=14)
    ax.margins(x=0.02)
    ax.set_title(title)

def share_ylims(axes, step=None):
    """Unify y range and hide y ticks on all but the first axis."""
    lo = min(ax.get_ylim()[0] for ax in axes)
    hi = max(ax.get_ylim()[1] for ax in axes)
    if step is None:
        span = hi - lo
        step = next(s for s in [0.25, 0.5, 1.0, 2.0, 5.0] if span / s <= 8)
    ticks = np.arange(np.floor(lo / step) * step, hi + step / 2, step)
    for i, ax in enumerate(axes):
        ax.set_ylim(lo, hi)
        ax.set_yticks(ticks)
        if i > 0:
            ax.set_yticklabels([])
            ax.tick_params(left=False)

def show_plots(cgra, hls):
    fig = plt.figure(figsize=(12, 5), layout="constrained")
    fig.get_layout_engine().set(w_pad=0, h_pad=0, hspace=0, wspace=0)
    # Use subfigures for each row so constrained_layout works correctly
    (top, bot) = fig.subfigures(2, 1, hspace=0.05, height_ratios=[1, 1])

    cgra_keys = ["wv", "rp_noopt", "rp"]
    hls_keys = ["wv", "crt"]

    # Row 1: two CGRA plots (relative to RipTide)
    (ax1, ax2) = top.subplots(1, 2, gridspec_kw={"wspace": 0.02})
    make_bar_plot(ax1, cgra, "steps", cgra_keys, "rp", "Relative Simulation Steps vs. RipTide")
    make_bar_plot(ax2, cgra, "graph_size", cgra_keys, "rp", "Relative #Operators vs. RipTide" if not mpl.rcParams.get("text.usetex") else "Relative \\#Operators vs. RipTide")
    ax2.legend(fontsize=14, loc="upper right", ncol=3, columnspacing=1, handletextpad=0.3, frameon=False,
               bbox_to_anchor=(1.02, 1.05))
    share_ylims([ax1, ax2])

    # Row 2: three HLS plots (relative to CIRCT), excluding "sort"
    (ax3, ax4, ax5) = bot.subplots(1, 3, gridspec_kw={"wspace": 0})
    make_bar_plot(ax3, hls, "exec_time", hls_keys, "crt",
                  "Relative Exec. Time vs. CIRCT", bench_names=BENCH_NAMES, x_rotation=45)
    make_bar_plot(ax4, hls, "luts", hls_keys, "crt",
                  "Relative #LUTs vs. CIRCT" if not mpl.rcParams.get("text.usetex") else "Relative \\#LUTs vs. CIRCT", bench_names=BENCH_NAMES, x_rotation=45)
    make_bar_plot(ax5, hls, "ffs", hls_keys, "crt",
                  "Relative #FFs vs. CIRCT" if not mpl.rcParams.get("text.usetex") else "Relative \\#FFs vs. CIRCT", bench_names=BENCH_NAMES, x_rotation=45)
    ax5.legend(fontsize=14, loc="upper right", ncol=2, columnspacing=1, handletextpad=0.3, frameon=False,
               bbox_to_anchor=(1.02, 1.05))
    share_ylims([ax3, ax4, ax5], step=0.5)

    return fig

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--plot", metavar="PDF_FILE", help="Generate bar plots and save to PDF")
    parser.add_argument("--no-tex", action="store_true", default=False, help="Disable LaTeX rendering in matplotlib")
    args = parser.parse_args()

    configure_mpl(use_tex=not args.no_tex)

    cgra = {name: collect_cgra(name) for name in BENCH_NAMES}
    hls = {name: collect_hls(name) for name in BENCH_NAMES}
    perf = {name: collect_compiler_perf(name) for name in BENCH_NAMES}
    print("% Generated by <wavelet-repo>/integration-tests/sim/stats.py")
    print()
    print(rf"\newcommand{{\numeval}}{{{len(BENCH_NAMES)}\xspace}}")
    print()
    print("%%%%%%%% CGRA Table %%%%%%%%")
    print(r"\newcommand{\evalcgra}{")
    print(generate_cgra_table(cgra))
    print("}")
    print()
    print("%%%%%%%% HLS Table %%%%%%%%")
    print(r"\newcommand{\evalhls}{")
    print(generate_hls_table(hls))
    print("}")
    print()
    print("%%%%%%%% Compiler Perf Table %%%%%%%%")
    print(r"\newcommand{\evalperf}{")
    print(generate_compiler_perf_table(perf))
    print("}")
    print()
    print("%%%%%%%% LoC Table %%%%%%%%")
    print(r"\newcommand{\evalloc}{")
    print(generate_loc_table())
    print("}")
    print()
    print("%%%%%%%% Other Stats %%%%%%%%")
    print(emit_stats(cgra, hls, perf))

    if args.plot:
        fig = show_plots(cgra, hls)
        fig.savefig(args.plot, format="pdf", bbox_inches="tight", pad_inches=0.03)
        print(f"% Plot saved to {args.plot}", file=__import__("sys").stderr)

if __name__ == "__main__":
    main()
