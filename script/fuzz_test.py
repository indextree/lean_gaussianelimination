#!/usr/bin/env python3
"""
Fuzz & Differential Testing Framework for lean_gaussianelimination.

This script tests the compiled Lean 4 executable (`lean_gaussianelimination`)
against an independent exact-rational (fractions.Fraction) oracle in Python.

For every tested n×n matrix M over ℚ, it verifies:
  1. Valid elementary operations: every trace step R_i ← R_i + c*R_j or C_i ← C_i + c*C_j
     has 0 <= i, j < n and i != j.
  2. Trace replay equivalence: applying the trace operations to M in exact rational
     arithmetic yields the exact `Final Matrix` reported by Lean.
  3. Diagonal form: `Final Matrix` has zeros everywhere off the main diagonal, and
     its diagonal matches `D[0..n-1]`.
  4. Determinant invariance: det(M) == prod(D[i]), since transvections have det = 1.
  5. Rank invariance: rank(M) == count(D[i] != 0), since transvections are invertible.

Usage:
  # Run default fuzz suite (200 random + edge-case matrices of sizes 1×1..6×6)
  python3 script/fuzz_test.py

  # Customize fuzz parameters
  python3 script/fuzz_test.py --num-tests 500 --max-size 7 --seed 42

  # Test custom matrix inputs with full trace + oracle verification
  python3 script/fuzz_test.py --matrix "[[0, 2, 3], [4, 5, 6], [7, 8, 10]]"
  python3 script/fuzz_test.py --matrix "0, 1/2; -3/4, 0"
  python3 script/fuzz_test.py --file path/to/matrices.txt
"""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import random
import re
import subprocess
import sys
import time
from typing import List, Optional, Sequence, Tuple

Matrix = List[List[Fraction]]


@dataclass
class ElemOp:
    kind: str  # "R" (addRow) or "C" (addCol)
    target: int
    source: int
    coeff: Fraction


@dataclass
class TraceResult:
    input_matrix: Matrix
    ops: List[ElemOp]
    diagonal: List[Fraction]
    final_matrix: Matrix
    raw_output: str


STEP_RE = re.compile(
    r"^Step\s+\d+:\s+([RC])(\d+)\s+←\s+[RC](\d+)\s+\+\s+\((.+)\)\s+\*\s+([RC])(\d+)\s*$"
)
DIAG_RE = re.compile(r"^D\[(\d+)\]\s*=\s*(.+?)\s*$")


def parse_lean_rat(text: str) -> Fraction:
    """Parse Lean's Repr output for ℚ (e.g. '(-7 : Rat)/4', '1', '-2') or user input."""
    cleaned = text.replace(": Rat", "")
    cleaned = "".join(ch for ch in cleaned if ch not in "()+ \t\r\n")
    if "/" in cleaned:
        num_s, den_s = cleaned.split("/", 1)
        return Fraction(int(num_s), int(den_s))
    return Fraction(int(cleaned), 1)


def parse_user_matrix(text: str) -> Matrix:
    """Parse a custom matrix string in JSON, semicolon, Lean !![...], or multiline format."""
    raw_chunks = re.split(r"[;\n\]]", text)
    row_strings: List[str] = []
    for chunk in raw_chunks:
        filtered = "".join(ch for ch in chunk if ch not in "[!]").strip()
        filtered = filtered.strip(", \t\r")
        if filtered:
            row_strings.append(filtered)
    if not row_strings:
        raise ValueError(f"Empty matrix input: {text!r}")

    rows: Matrix = []
    for r_str in row_strings:
        if "," in r_str:
            tokens = [t.strip() for t in r_str.split(",") if t.strip()]
        else:
            tokens = [t.strip() for t in r_str.split() if t.strip()]
        rows.append([parse_lean_rat(tok) for tok in tokens])

    n = len(rows)
    for r in rows:
        if len(r) != n:
            raise ValueError(f"Matrix must be square: {n} rows, but row has {len(r)} entries")
    return rows


def format_matrix_for_cli(mat: Matrix) -> str:
    """Format a matrix as a single-line nested list string '[[...], [...]]' for the Lean CLI."""
    row_strs = []
    for row in mat:
        entries = [
            f"{val.numerator}" if val.denominator == 1 else f"{val.numerator}/{val.denominator}"
            for val in row
        ]
        row_strs.append("[" + ", ".join(entries) + "]")
    return "[" + ", ".join(row_strs) + "]"


def parse_matrix_block(lines: List[str]) -> Matrix:
    """Parse a printed matrix block of lines like '  [1, 0, (-7 : Rat)/4]'."""
    mat: Matrix = []
    for line in lines:
        s = line.strip()
        if not (s.startswith("[") and s.endswith("]")):
            raise ValueError(f"Unexpected matrix row line: {line!r}")
        inner = s[1:-1].strip()
        if not inner:
            mat.append([])
        else:
            tokens = [tok.strip() for tok in inner.split(",")]
            mat.append([parse_lean_rat(tok) for tok in tokens])
    return mat


def parse_single_trace_output(raw_block: str) -> TraceResult:
    """Parse one complete output block from `lean_gaussianelimination`."""
    lines = [line.rstrip() for line in raw_block.strip().splitlines()]
    idx = 0
    n_lines = len(lines)

    while idx < n_lines and lines[idx].strip() != "Input Matrix:":
        idx += 1
    if idx >= n_lines:
        raise ValueError(f"Missing 'Input Matrix:' header in output:\n{raw_block}")
    idx += 1

    input_rows: List[str] = []
    while idx < n_lines and lines[idx].strip().startswith("["):
        input_rows.append(lines[idx])
        idx += 1
    input_matrix = parse_matrix_block(input_rows)

    while idx < n_lines and lines[idx].strip() != "=== Gaussian Elimination Trace ===":
        idx += 1
    if idx >= n_lines:
        raise ValueError(f"Missing trace header in output:\n{raw_block}")
    idx += 1

    ops: List[ElemOp] = []
    while idx < n_lines and lines[idx].strip().startswith("Step "):
        m = STEP_RE.match(lines[idx].strip())
        if not m:
            raise ValueError(f"Could not parse trace step line: {lines[idx]!r}")
        kind1, i1, i2, coeff_str, kind2, j = m.groups()
        if kind1 != kind2 or int(i1) != int(i2):
            raise ValueError(f"Malformed operation line: {lines[idx]!r}")
        ops.append(
            ElemOp(
                kind=kind1,
                target=int(i1),
                source=int(j),
                coeff=parse_lean_rat(coeff_str),
            )
        )
        idx += 1

    while idx < n_lines and lines[idx].strip() != "=== Final Diagonal ===":
        idx += 1
    if idx >= n_lines:
        raise ValueError(f"Missing diagonal header in output:\n{raw_block}")
    idx += 1

    diagonal: List[Fraction] = []
    while idx < n_lines and lines[idx].strip().startswith("D["):
        m = DIAG_RE.match(lines[idx].strip())
        if not m:
            raise ValueError(f"Could not parse diagonal line: {lines[idx]!r}")
        d_idx, val_str = m.groups()
        if int(d_idx) != len(diagonal):
            raise ValueError(f"Out-of-order diagonal index in line: {lines[idx]!r}")
        diagonal.append(parse_lean_rat(val_str))
        idx += 1

    while idx < n_lines and lines[idx].strip() != "Final Matrix:":
        idx += 1
    if idx >= n_lines:
        raise ValueError(f"Missing 'Final Matrix:' header in output:\n{raw_block}")
    idx += 1

    final_rows: List[str] = []
    while idx < n_lines and lines[idx].strip().startswith("["):
        final_rows.append(lines[idx])
        idx += 1
    final_matrix = parse_matrix_block(final_rows)

    return TraceResult(
        input_matrix=input_matrix,
        ops=ops,
        diagonal=diagonal,
        final_matrix=final_matrix,
        raw_output=raw_block,
    )


def apply_ops_oracle(mat: Matrix, ops: Sequence[ElemOp]) -> Matrix:
    """Replay elementary operations in exact rational arithmetic."""
    n = len(mat)
    cur = copy.deepcopy(mat)
    for step_idx, op in enumerate(ops, start=1):
        if not (0 <= op.target < n and 0 <= op.source < n):
            raise AssertionError(
                f"Step {step_idx}: out-of-bounds indices ({op.target}, {op.source}) for n={n}"
            )
        if op.target == op.source:
            raise AssertionError(
                f"Step {step_idx}: invalid transvection with equal indices i == j == {op.target}"
            )
        if op.kind == "R":
            for col in range(n):
                cur[op.target][col] += op.coeff * cur[op.source][col]
        elif op.kind == "C":
            for row in range(n):
                cur[row][op.target] += op.coeff * cur[row][op.source]
        else:
            raise AssertionError(f"Step {step_idx}: unknown op kind {op.kind!r}")
    return cur


def det_and_rank_oracle(mat: Matrix) -> Tuple[Fraction, int]:
    """Compute exact determinant and rank of an n×n rational matrix."""
    n = len(mat)
    a = copy.deepcopy(mat)
    det = Fraction(1, 1)
    rank = 0
    row = 0

    for col in range(n):
        pivot = None
        for r in range(row, n):
            if a[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            det = Fraction(0, 1)
            continue
        if pivot != row:
            a[row], a[pivot] = a[pivot], a[row]
            det = -det
        piv_val = a[row][col]
        det *= piv_val
        rank += 1
        for r in range(row + 1, n):
            if a[r][col] != 0:
                factor = a[r][col] / piv_val
                for c in range(col, n):
                    a[r][c] -= factor * a[row][c]
        row += 1

    if rank < n:
        det = Fraction(0, 1)
    return det, rank


def verify_trace_result(expected_input: Matrix, res: TraceResult) -> None:
    """Run all 5 oracle checks on a parsed TraceResult."""
    n = len(expected_input)
    if res.input_matrix != expected_input:
        raise AssertionError(
            f"Parsed input matrix does not match expected input.\n"
            f"Expected: {expected_input}\nGot: {res.input_matrix}"
        )

    # 1 & 2. Validate operations and replay trace
    replayed = apply_ops_oracle(expected_input, res.ops)
    if replayed != res.final_matrix:
        raise AssertionError(
            f"Replayed matrix does not match Lean's Final Matrix!\n"
            f"Input: {expected_input}\n"
            f"Replayed: {replayed}\n"
            f"Lean Final: {res.final_matrix}\n"
            f"Trace:\n{res.raw_output}"
        )

    # 3. Check Final Matrix is strictly diagonal and matches D
    if len(res.diagonal) != n:
        raise AssertionError(f"Expected diagonal of length {n}, got {len(res.diagonal)}")
    for i in range(n):
        for j in range(n):
            if i == j:
                if res.final_matrix[i][j] != res.diagonal[i]:
                    raise AssertionError(
                        f"Diagonal mismatch at ({i},{i}): matrix has {res.final_matrix[i][j]}, "
                        f"D[{i}] is {res.diagonal[i]}"
                    )
            else:
                if res.final_matrix[i][j] != 0:
                    raise AssertionError(
                        f"Final Matrix is NOT diagonal! Off-diagonal entry at ({i},{j}) = "
                        f"{res.final_matrix[i][j]}\nTrace:\n{res.raw_output}"
                    )

    # 4 & 5. Check determinant and rank preservation
    expected_det, expected_rank = det_and_rank_oracle(expected_input)
    diag_det = Fraction(1, 1)
    for d in res.diagonal:
        diag_det *= d
    diag_rank = sum(1 for d in res.diagonal if d != 0)

    if expected_det != diag_det:
        raise AssertionError(
            f"Determinant mismatch! det(M) = {expected_det}, prod(D) = {diag_det}\n"
            f"Input: {expected_input}\nTrace:\n{res.raw_output}"
        )
    if expected_rank != diag_rank:
        raise AssertionError(
            f"Rank mismatch! rank(M) = {expected_rank}, non-zero diagonal count = {diag_rank}\n"
            f"Input: {expected_input}\nTrace:\n{res.raw_output}"
        )


# ---------------------------------------------------------------------------
# Fuzz Matrix Generators
# ---------------------------------------------------------------------------

def rand_rat(rng: random.Random, max_num: int = 8, max_den: int = 1) -> Fraction:
    num = rng.randint(-max_num, max_num)
    den = rng.randint(1, max_den)
    return Fraction(num, den)


def deterministic_edge_cases() -> List[Tuple[str, Matrix]]:
    """Curated edge cases covering pivot row swaps, pivot col swaps, singular & zero matrices."""
    raw_cases = [
        ("edge_1x1_zero", "[[0]]"),
        ("edge_1x1_nonzero", "[[-3/5]]"),
        ("edge_2x2_perm", "[[0, 1], [1, 0]]"),
        ("edge_2x2_row_pivot_only", "[[0, 1], [0, 0]]"),
        ("edge_2x2_col_pivot_only", "[[0, 0], [1, 0]]"),
        ("edge_2x2_bottom_right_only", "[[0, 0], [0, 7]]"),
        ("edge_2x2_zero", "[[0, 0], [0, 0]]"),
        ("edge_3x3_pivot_swap", "[[0, 2, 3], [4, 5, 6], [7, 8, 10]]"),
        ("edge_3x3_antidiag", "[[0, 0, 1], [0, 2, 0], [3, 0, 0]]"),
        ("edge_3x3_cyclic_perm", "[[0, 1, 0], [0, 0, 1], [1, 0, 0]]"),
        ("edge_3x3_zero_first_col", "[[0, 3, -1], [0, 0, 5], [0, 0, 0]]"),
        ("edge_3x3_zero_first_row", "[[0, 0, 0], [2, 0, 4], [-1, 3, 0]]"),
        ("edge_4x4_checkerboard_pivot", "[[0, 1, 0, 2], [3, 0, 4, 0], [0, 5, 0, 6], [7, 0, 8, 1]]"),
        ("edge_4x4_late_pivot", "[[1, 0, 0, 0], [0, -4, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]"),
    ]
    return [(name, parse_user_matrix(spec)) for name, spec in raw_cases]


def generate_fuzz_cases(num_tests: int, max_size: int, seed: int) -> List[Tuple[str, Matrix]]:
    rng = random.Random(seed)
    cases: List[Tuple[str, Matrix]] = []
    cases.extend(deterministic_edge_cases())

    categories = [
        "zero_diagonal",
        "pivot_row_swap",
        "pivot_col_swap",
        "singular_rank_deficient",
        "sparse_random",
        "random_rational",
    ]

    for i in range(num_tests):
        cat = categories[i % len(categories)]
        n = rng.randint(2, max(2, max_size))

        if cat == "zero_diagonal":
            mat = [[rand_rat(rng, 6, 2) for _ in range(n)] for _ in range(n)]
            for k in range(n):
                mat[k][k] = Fraction(0, 1)

        elif cat == "pivot_row_swap":
            mat = [[rand_rat(rng, 6, 1) for _ in range(n)] for _ in range(n)]
            # Force several diagonal entries to 0 while ensuring some entry below is non-zero
            for k in range(n - 1):
                if rng.random() < 0.75:
                    mat[k][k] = Fraction(0, 1)
                    piv_r = rng.randint(k + 1, n - 1)
                    if mat[piv_r][k] == 0:
                        mat[piv_r][k] = Fraction(rng.choice([-3, -2, -1, 1, 2, 3]), 1)

        elif cat == "pivot_col_swap":
            mat = [[rand_rat(rng, 5, 1) for _ in range(n)] for _ in range(n)]
            # Zero out an entire column k while keeping a non-zero entry in row k to the right
            col_k = rng.randint(0, n - 2)
            for r in range(n):
                mat[r][col_k] = Fraction(0, 1)
            piv_c = rng.randint(col_k + 1, n - 1)
            if mat[col_k][piv_c] == 0:
                mat[col_k][piv_c] = Fraction(rng.choice([-4, -1, 1, 2, 5]), 1)

        elif cat == "singular_rank_deficient":
            target_rank = rng.randint(0, n - 1)
            if target_rank == 0:
                mat = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
            else:
                left = [[rand_rat(rng, 4, 1) for _ in range(target_rank)] for _ in range(n)]
                right = [[rand_rat(rng, 4, 1) for _ in range(n)] for _ in range(target_rank)]
                mat = [
                    [
                        sum(left[r][t] * right[t][c] for t in range(target_rank))
                        for c in range(n)
                    ]
                    for r in range(n)
                ]

        elif cat == "sparse_random":
            mat = [
                [
                    rand_rat(rng, 5, 2) if rng.random() < 0.3 else Fraction(0, 1)
                    for _ in range(n)
                ]
                for _ in range(n)
            ]

        else:  # random_rational
            mat = [[rand_rat(rng, 6, 4) for _ in range(n)] for _ in range(n)]

        cases.append((cat, mat))

    return cases


def ensure_binary(repo_root: Path, build_if_missing: bool = True) -> Path:
    bin_path = repo_root / ".lake" / "build" / "bin" / "lean_gaussianelimination"
    if not bin_path.exists():
        if not build_if_missing:
            raise FileNotFoundError(f"Executable not found at {bin_path}")
        print("[*] Building lean_gaussianelimination via `lake build`...")
        subprocess.run(["lake", "build"], cwd=repo_root, check=True)
    return bin_path


def run_batch_via_stdin(bin_path: Path, matrices: Sequence[Matrix]) -> List[TraceResult]:
    """Run a batch of matrices through `lean_gaussianelimination --stdin` in one invocation."""
    stdin_payload = "\n".join(format_matrix_for_cli(m) for m in matrices) + "\n"
    proc = subprocess.run(
        [str(bin_path), "--stdin"],
        input=stdin_payload,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"lean_gaussianelimination exited with code {proc.returncode}:\n"
            f"STDERR:\n{proc.stderr}\nSTDOUT:\n{proc.stdout}"
        )
    raw_blocks = [b.strip() for b in proc.stdout.split("════════════════════════════════════") if b.strip()]
    if len(raw_blocks) != len(matrices):
        raise RuntimeError(
            f"Expected {len(matrices)} output blocks, got {len(raw_blocks)}.\n"
            f"Raw stdout:\n{proc.stdout}"
        )
    return [parse_single_trace_output(block) for block in raw_blocks]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Fuzz test & custom input verifier for lean_gaussianelimination"
    )
    parser.add_argument(
        "-n", "--num-tests", type=int, default=200,
        help="Number of random fuzz matrices to generate (default: 200)"
    )
    parser.add_argument(
        "--max-size", type=int, default=6,
        help="Maximum matrix dimension n for random n×n matrices (default: 6)"
    )
    parser.add_argument(
        "--seed", type=int, default=20261018,
        help="Random seed for reproducible fuzzing (default: 20261018)"
    )
    parser.add_argument(
        "-m", "--matrix", action="append", default=[],
        help="Custom matrix string to execute and verify (can be specified multiple times)"
    )
    parser.add_argument(
        "-f", "--file", type=str, default=None,
        help="Path to file containing one or more custom matrices to execute and verify"
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Print detailed trace output for tested matrices"
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    bin_path = ensure_binary(repo_root)

    # Mode 1: Custom inputs (--matrix or --file)
    if args.matrix or args.file:
        custom_matrices: List[Matrix] = []
        for m_str in args.matrix:
            custom_matrices.append(parse_user_matrix(m_str))
        if args.file:
            content = Path(args.file).read_text(encoding="utf-8")
            lines = [
                l.strip() for l in content.splitlines()
                if l.strip() and not l.strip().startswith("#")
            ]
            if all((";" in l or l.startswith("[[") or l.startswith("!![")) for l in lines):
                for l in lines:
                    custom_matrices.append(parse_user_matrix(l))
            else:
                for block in content.split("---"):
                    if block.strip():
                        custom_matrices.append(parse_user_matrix(block))

        results = run_batch_via_stdin(bin_path, custom_matrices)
        for idx, (mat, res) in enumerate(zip(custom_matrices, results), start=1):
            print(res.raw_output)
            verify_trace_result(mat, res)
            det, rank = det_and_rank_oracle(mat)
            print(
                f"\n[✓] Oracle Verified (Matrix #{idx}, {len(mat)}×{len(mat)}, "
                f"steps={len(res.ops)}, rank={rank}, det={det})"
            )
            if idx < len(custom_matrices):
                print("\n" + "═" * 44 + "\n")
        return 0

    # Mode 2: Fuzz testing suite
    start_time = time.time()
    cases = generate_fuzz_cases(args.num_tests, args.max_size, args.seed)
    matrices = [m for _, m in cases]

    print(
        f"=== Running Gaussian Elimination Fuzz Suite ===\n"
        f"Binary   : {bin_path}\n"
        f"Total    : {len(cases)} matrices ({len(deterministic_edge_cases())} edge cases + {args.num_tests} random)\n"
        f"Max size : {args.max_size}×{args.max_size}\n"
        f"Seed     : {args.seed}\n"
    )

    results = run_batch_via_stdin(bin_path, matrices)

    cat_counts: dict[str, int] = {}
    total_ops = 0
    for idx, ((cat, mat), res) in enumerate(zip(cases, results), start=1):
        try:
            verify_trace_result(mat, res)
        except Exception as exc:
            print(f"\n[✗] FAILURE on test #{idx} (category={cat}):")
            print(f"Reproducer CLI command:")
            print(f'  lake exe lean_gaussianelimination "{format_matrix_for_cli(mat)}"')
            print(f"Error: {exc}")
            return 1

        bucket = "edge_cases" if cat.startswith("edge_") else cat
        cat_counts[bucket] = cat_counts.get(bucket, 0) + 1
        total_ops += len(res.ops)
        if args.verbose:
            print(f"[✓] #{idx:03d} [{cat}] ({len(mat)}×{len(mat)}, {len(res.ops)} ops)")

    elapsed = time.time() - start_time
    print("Category Breakdown:")
    for cat_name, count in sorted(cat_counts.items()):
        print(f"  • {cat_name:<26}: {count:>4} passed")
    print(
        f"\n[✓] All {len(cases)}/{len(cases)} fuzz tests passed! "
        f"(replayed {total_ops} elementary operations in {elapsed:.2f}s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
