import re
import json


def main():
    tests = [
        ("rt", "bfs", "Breadth-first search (RipTide)", True),
        ("rt", "dconv", "Dense convolution (RipTide)", True),
        ("rt", "dfs", "Depth-first search (RipTide)", True),
        ("rt", "dmm", "Dense-dense matrix mult. (RipTide)", True),
        ("rt", "dmv", "Dense-dense matrix-vector mult. (RipTide)", True),
        ("rt", "fft", "Fast Fourier transform (RipTide)", True),
        ("rt", "sconv", "Sparse convolution (RipTide)", True),
        ("rt", "smm", "Sparse-dense matrix mult. (RipTide)", True),
        ("rt", "smv", "Sparse-dense matrix-vector mult. (Pipestitch)", True),
        ("rt", "sort", "Radix sort (RipTide)", False),
        ("nn", "nn_conv", "Neural network convolution layer (RipTide)", True),
        ("nn", "nn_fc", "Neural network fully-connected layer (RipTide)", True),
        ("nn", "nn_norm", "Neural network normalization (RipTide)", True),
        ("nn", "nn_pool", "Neural network pooling layer (RipTide)", True),
        ("nn", "nn_relu", "Neural network ReLU layer (RipTide)", True),
        ("nn", "nn_vadd", "Vector addition (RipTide)", True),
        ("ps", "Dither", "Dithering (Pipestitch)", True),
        ("ps", "SpMSpMd", "Sparse-sparse matrix mult. (Pipestitch)", True),
        ("ps", "SpMSpVd", "Sparse-sparse matrix-vector mult. (Pipestitch)", True),
        ("ps", "SpSlice", "Sparse matrix slicing (Pipestitch)", False),
        ("", "sha256", "SHA-256 hash", False),
    ]

    lines = []

    for source, test, description, success in tests:
        with open(f"{test}.{test}.lso.ll") as f:
            llvm_loc = len(f.readlines())

        with open(f"{test}.c") as f:
            c_loc = len(f.readlines())

        with open(f"{test}.{test}.o2p") as f:
            num_operators = len(json.load(f)["vertices"])

        with open(f"{test}.{test}.o2p") as f:
            o2p = f.read()
            num_mem_operators = o2p.count("MEM_CFG_OP_")
            num_st_operators = o2p.count("MEM_CFG_OP_STORE")
            num_ld_operators = o2p.count("MEM_CFG_OP_LOAD")

        with open(f"{test}.bisim.out") as f:
            content = f.read()
            num_cut_points = content.count("[simulation] llvm cut point") + 1

            match = re.search(r"\[simulation\] bisim check took ((\d+)\.(\d+))s", content)
            assert match is not None
            bisim_time = float(match.group(1))

            match = re.search(r"\[simulation\] confluence check took ((\d+)\.(\d+))s", content)
            assert match is not None
            confluence_time = float(match.group(1))

            match = re.search(r"\[simulation\] checking sat of (\d+) memory permission constraints", content)
            assert match is not None
            num_perm_constraints = int(match.group(1))

        test_name = test.replace("_", "\\textunderscore ")
        
        # if source != "nn" and source != "":
        #     prefix = source + "\\textunderscore "
        # else:
        #     prefix = ""

        bisim_time_prefix = "$\\times$ " if not success else ""
        line = f"\\texttt{{{test_name}}} & {c_loc} & {num_operators} & {num_perm_constraints} & {bisim_time_prefix}{bisim_time} & {confluence_time} & {description} \\\\"

        lines.append((num_operators, line))

    lines.sort(key=lambda l: l[0])
    for _, line in lines:
        print(line)


if __name__ == "__main__":
    main()
