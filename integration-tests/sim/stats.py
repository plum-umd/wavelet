"""
Collects stats from compilation results and generates LaTeX tables
comparing Wavelet, Wavelet without optimizations, RipTide (CGRA),
and CIRCT (HLS).
"""

from __future__ import annotations

import re
import json

from pathlib import Path

TESTS_DIR = Path(__file__).parent.parent / "tests"

BENCH_NAMES = [
    "nn_vadd", "nn_norm", "nn_relu", "nn_pool",
    "nn_fc", "nn_conv", "dmv", "dmm", "dither", "sort",
]

TRIVIAL_OPS = { "fork", "forward", "const", "sink", "inact" } 
CF_OPS = { "switch", "steer", "merge", "carry", "order", "forwardc", "inv" }
MEM_OPS = { "load", "store" }

def test_path(name: str, suffix: str) -> Path:
    return TESTS_DIR / name.replace("_", "-") / f"test.{suffix}"

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

def parse_rtl_cycles(path: Path) -> int | None:
    """Assuming simulation clock period is 1 ns."""
    text = read_file(path)
    if text is None:
        return None
    # Match the summary TESTS= line's SIM_TIME field
    m = re.search(r"SKIP=\d+\s+([0-9.]+)", text)
    return int(float(m.group(1))) if m else None

def parse_graph_size_wavelet(path: Path) -> int | None:
    """From compile log: '[optimization] N (M non-trivial) ops' -> M"""
    text = read_file(path)
    if text is None:
        return None
    m = re.search(r"\[optimization\]\s+\d+\s+\((\d+)\s+non-trivial\)", text)
    return int(m.group(1)) if m else None

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
    return {"luts": luts, "ffs": ffs, "freq_mhz": freq_mhz}

def cf_overhead(stats: tuple[int, int, int] | None) -> float | None:
    """cf_ops / (sync_ops + mem_ops)"""
    if stats is None:
        return None
    cf, sync, mem = stats
    denom = sync + mem
    return round(cf / denom, 2) if denom else None

def collect_cgra(name: str) -> dict:
    """Collect all CGRA table columns for one benchmark."""
    # Steps: total cycles from high-level dataflow simulation
    steps_wv = parse_total_cycles(test_path(name, "wavelet-sim.log"))
    steps_wv_noopt = parse_total_cycles(test_path(name, "wavelet-noopt-sim.log"))
    steps_rp = parse_total_cycles(test_path(name, "riptide-sim.log"))

    # Graph sizes: non-trivial ops from compile log (wavelet), vertex count (riptide)
    gs_wv = parse_graph_size_wavelet(test_path(name, "wavelet.json.log"))
    gs_wv_noopt = parse_graph_size_wavelet(test_path(name, "wavelet-noopt.json.log"))
    gs_rp = parse_graph_size_riptide(test_path(name, "riptide.json"))

    # CF ops and overhead from dataflow graph JSON
    wv_cf = parse_wavelet_cf_stats(test_path(name, "wavelet.json"))
    wv_noopt_cf = parse_wavelet_cf_stats(test_path(name, "wavelet-noopt.json"))
    rp_cf = parse_riptide_cf_stats(test_path(name, "riptide.json"))

    return {
        "steps": { "wv": steps_wv, "wv_noopt": steps_wv_noopt, "rp": steps_rp },
        "graph_size": { "wv": gs_wv, "wv_noopt": gs_wv_noopt, "rp": gs_rp },
        "cf_ops": {
            "wv": wv_cf[0] if wv_cf else None,
            "wv_noopt": wv_noopt_cf[0] if wv_noopt_cf else None,
            "rp": rp_cf[0] if rp_cf else None,
        },
        "cf_overhead": {
            "wv": cf_overhead(wv_cf),
            "wv_noopt": cf_overhead(wv_noopt_cf),
            "rp": cf_overhead(rp_cf),
        },
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

    return {
        "cycles": { "wv": cyc_wv, "wv_noopt": cyc_wv_noopt, "crt": cyc_crt },
        "exec_time": {
            "wv": exec_time(cyc_wv, pnr_wv),
            "wv_noopt": exec_time(cyc_wv_noopt, pnr_wv_noopt),
            "crt": exec_time(cyc_crt, pnr_crt),
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
    return f"\\texttt{{{name.replace('_', chr(92) + 'textunderscore{}')}}}"

def emit_table(
    all_stats: dict[str, dict],
    # (header, dict key, decimal places)
    metrics: list[tuple[str, str, int]],
    # (display label, dict key in inner dicts)
    compilers: list[tuple[str, str]],
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
        cells = [tt_name(name)]
        for _, metric_key, decimals in metrics:
            metric = stats[metric_key]
            for _, comp_key in compilers:
                cells.append(to_cell(metric[comp_key], decimals))
        lines.append(" & ".join(cells) + r" \\")

    lines.append(r"\end{tabular}")
    return "\n".join(lines)

def generate_cgra_table(all_stats: dict[str, dict]) -> str:
    return emit_table(
        all_stats,
        metrics=[
            ("Steps",        "steps",       0),
            ("Graph Sizes",  "graph_size",  0),
            ("CF Ops",       "cf_ops",      0),
            ("CF Overhead",  "cf_overhead", 2),
        ],
        compilers=[
            (r"\textbf{Wv}",     "wv"),
            (r"\textbf{Wv}$^*$", "wv_noopt"),
            ("RP",               "rp"),
        ],
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
    )

def main():
    cgra = {name: collect_cgra(name) for name in BENCH_NAMES}
    hls = {name: collect_hls(name) for name in BENCH_NAMES}
    print(generate_cgra_table(cgra))
    print()
    print(generate_hls_table(hls))

if __name__ == "__main__":
    main()
