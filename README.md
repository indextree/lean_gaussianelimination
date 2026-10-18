# Verified Gaussian Elimination in Lean 4

A formally verified implementation of Gaussian elimination using the Lean 4 theorem prover and Mathlib. This project demonstrates how to combine mathematical proofs with executable code.

## What is This Project?

This repository provides:

1. **Verified Gaussian Elimination** - A mathematically proven correct implementation that guarantees any matrix can be reduced to diagonal form using elementary row/column operations.

2. **Executable Trace** - A computable version that shows step-by-step which operations are performed during the elimination process.

## How Gaussian Elimination Works

Gaussian elimination reduces a matrix to diagonal form through **elementary operations**:

- **Row operation**: $R_i \leftarrow R_i + c \cdot R_j$ (add a multiple of row $j$ to row $i$)
- **Column operation**: $C_i \leftarrow C_i + c \cdot C_j$ (add a multiple of column $j$ to column $i$)

### Example

For the matrix:
```
[1, 2, 3]
[4, 5, 6]
[7, 8, 10]
```

The algorithm performs:
```
Step 1: R1 ← R1 + (-4) * R0    → Eliminate M[1,0]
Step 2: R2 ← R2 + (-7) * R0    → Eliminate M[2,0]
Step 3: C1 ← C1 + (-2) * C0    → Eliminate M[0,1]
Step 4: C2 ← C2 + (-3) * C0    → Eliminate M[0,2]
Step 5: R2 ← R2 + (-2) * R1    → Eliminate M[2,1]
Step 6: C2 ← C2 + (-2) * C1    → Eliminate M[1,2]
```

Result: Diagonal matrix `[1, -3, 1]`

## Mathematical Foundation

### The Core Theorem

For any matrix $M$ over a field $K$, there exist:
- Lists of transvections $L$ (row operations) and $L'$ (column operations)
- A diagonal function $D$

Such that:

$$(\prod L) \cdot M \cdot (\prod L') = \text{diagonal}(D)$$

This is proven in Mathlib as `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`.

### What is a Transvection?

A **transvection** is an elementary matrix that represents adding a multiple of one row/column to another. In Mathlib, this is represented by `Matrix.TransvectionStruct`.

### Certificate-Based Verification

Instead of just computing a result, this project produces a **certificate** containing:
- `L` : List of left transvections (row operations)
- `L'` : List of right transvections (column operations)  
- `D` : The diagonal entries
- `h` : A **proof** that `L * M * L' = diagonal(D)`

This means the result is mathematically guaranteed to be correct!

## How This Repository Works

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                         Main.lean                                │
│                    (Entry point & examples)                      │
└──────────────────────────┬──────────────────────────────────────┘
                           │
          ┌────────────────┴────────────────┐
          ▼                                 ▼
┌─────────────────────────┐    ┌─────────────────────────────────┐
│ LeanGaussianelimination │    │ LeanGaussianelimination/        │
│        .lean            │    │      Computable.lean            │
│                         │    │                                 │
│  • GaussCert structure  │    │  • ElemOp type                  │
│  • gaussianElim         │    │  • gaussianElimWithTrace        │
│  • GaussFactor          │    │  • gaussianElimWithTrace_spec   │
│  • Proofs via Mathlib   │    │  • gaussianElimComputable       │
│                         │    │  • Step-by-step execution       │
│  (Noncomputable -       │    │  (Computable & formally proven  │
│   Mathlib witness)      │    │   correct for any matrix)       │
└─────────────────────────┘    └─────────────────────────────────┘
          │                                 │
          └────────────────┬────────────────┘
                           ▼
              ┌─────────────────────────┐
              │        Mathlib          │
              │                         │
              │  • Matrix type          │
              │  • TransvectionStruct   │
              │  • Pivot theorems       │
              │  • Field operations     │
              └─────────────────────────┘
```

### Detailed Code Flow

#### 1. Verified Implementation (`LeanGaussianelimination.lean`)

This file provides the **mathematically verified** certificate structures and Mathlib witness extraction:

```lean
-- Certificate structure: contains the result AND its proof
structure GaussCert (M : Matrix n n K) where
  L  : List (Matrix.TransvectionStruct n K)   -- Row operations
  L' : List (Matrix.TransvectionStruct n K)   -- Column operations
  D  : n → K                                   -- Diagonal entries
  h  : transvecProd L * M * transvecProd L' = Matrix.diagonal D  -- PROOF!

-- Extract certificate from Mathlib's existence theorem
noncomputable def gaussianElim (M : Matrix n n K) : GaussCert M :=
  -- Uses Classical.choose to extract witnesses from:
  -- Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
  ...
```

#### 2. Computable & Formally Verified Implementation (`Computable.lean`)

This file provides the **executable** version with trace output AND formal proofs (`gaussianElimWithTrace_spec`, `gaussianElimComputable`, `gaussianFactorComputable`) connecting it to `GaussCert` and `GaussFactor` for any general matrix:

```lean
-- Elementary operation type
inductive ElemOp (n : ℕ) (K : Type*) where
  | addRow (i j : Fin n) (c : K) (h : i ≠ j)  -- Rᵢ ← Rᵢ + c * Rⱼ
  | addCol (i j : Fin n) (c : K) (h : i ≠ j)  -- Cᵢ ← Cᵢ + c * Cⱼ

-- Apply an operation to a matrix
def applyOp (M : Matrix (Fin n) (Fin n) K) : ElemOp n K → Matrix (Fin n) (Fin n) K
  | .addRow i j c _ => M.updateRow i (M i + c • M j)
  | .addCol i j c _ => Matrix.updateCol M i (fun k => M k i + c * M k j)
```

**The elimination algorithm:**

```
gaussElimLoop(M, k, ops):
  if k ≥ n: return (ops, M)
  
  pivotRow ← findPivot(M, column=k, startRow=k)
  if pivotRow is None:
    pivotCol ← findRowPivot(M, row=k, startCol=k)
    if pivotCol is None:
      return gaussElimLoop(M, k+1, ops)  // Row and column k already zero
    // Move non-zero entry in row k into (k, k) via column operation
    prepOp ← addCol(k, pivotCol, 1)
    M0 ← applyOp(M, prepOp)
    (colOps, M')  ← eliminateColumn(M0, k, k)
    (rowOps, M'') ← eliminateRow(M', k, k)
    return gaussElimLoop(M'', k+1, ops ++ [prepOp] ++ colOps ++ rowOps)

  if pivotRow ≠ k:
    // Move non-zero entry in column k into (k, k) via row operation
    prepOp ← addRow(k, pivotRow, 1)
    M0 ← applyOp(M, prepOp)
  else:
    M0 ← M
  
  // Eliminate all other entries in column k using row k as pivot
  (colOps, M') ← eliminateColumn(M0, k, k)
  
  // Eliminate all other entries in row k using column k as pivot
  (rowOps, M'') ← eliminateRow(M', k, k)
  
  return gaussElimLoop(M'', k+1, ops ++ prepOps ++ colOps ++ rowOps)
```

#### 3. How Operations Are Recorded

Each step is recorded as an `ElemOp`:

```lean
def eliminateEntry (M : Matrix) (i pivotRow j : Fin n) :=
  let c := -(M i j) / (M pivotRow j)        -- Compute multiplier
  let op := ElemOp.addRow i pivotRow c ...  -- Record operation
  let M' := applyOp M op                    -- Apply to matrix
  (op, M')                                  -- Return both
```

#### 4. Printing the Trace

```lean
def printTrace (trace : GaussTrace n K) : IO Unit := do
  for op in trace.ops do
    IO.println s!"{op.toString}"  -- "R1 ← R1 + (-4) * R0"
```

### Data Flow Example

For input matrix `!![1, 2; 3, 4]`:

```
Input: M = [1, 2]
           [3, 4]

Step 1: findPivot(col=0) → row 0 (value=1)
        eliminateColumn: R1 ← R1 + (-3)*R0
        M' = [1, 2]
             [0, -2]
        
        eliminateRow: C1 ← C1 + (-2)*C0  
        M'' = [1, 0]
              [0, -2]

Step 2: findPivot(col=1) → row 1 (value=-2)
        No other entries to eliminate

Output: ops = [addRow(1,0,-3), addCol(1,0,-2)]
        diagonal = [1, -2]
        finalMatrix = [1, 0; 0, -2]
```

## Project Structure

```
lean_gaussianelimination/
├── LeanGaussianelimination.lean      # Verified certificate structures & Mathlib witnesses
├── LeanGaussianelimination/
│   ├── Basic.lean                    # Basic definitions
│   └── Computable.lean               # Executable implementation, trace & formal proofs
├── Main.lean                         # CLI entry point (built-in examples & custom inputs)
├── script/
│   ├── fuzz_test.py                  # Differential fuzz test & oracle verifier over ℚ
│   ├── run_fuzz.sh                   # Shell runner for fuzz tests & custom inputs
│   └── sample_matrices.txt           # Sample custom matrix inputs
├── lakefile.toml                     # Build configuration
└── lean-toolchain                    # Lean version specification
```

## Getting Started

### Prerequisites

1. **Install Lean 4 and Elan** (Lean version manager):

   ```bash
   # On macOS/Linux
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   
   # On Windows (PowerShell)
   curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
   powershell -ExecutionPolicy Bypass -File elan-init.ps1
   ```

2. **Restart your terminal** or run:
   ```bash
   source ~/.profile  # or ~/.bashrc, ~/.zshrc depending on your shell
   ```

3. **Verify installation**:
   ```bash
   lean --version
   lake --version
   ```

### Building and Running

1. **Clone the repository**:
   ```bash
   git clone https://github.com/yourusername/lean_gaussianelimination.git
   cd lean_gaussianelimination
   ```

2. **Download dependencies** (this downloads Mathlib, may take a few minutes):
   ```bash
   lake update
   ```

3. **Build the project**:
   ```bash
   lake build
   ```

4. **Run the built-in examples**:
   ```bash
   lake exe lean_gaussianelimination
   ```

5. **Run with custom matrix inputs**:
   ```bash
   # JSON / nested list format
   lake exe lean_gaussianelimination "[[0, 2, 3], [4, 5, 6], [7, 8, 10]]"

   # Semicolon-separated rows (supports integers and rational fractions a/b)
   lake exe lean_gaussianelimination "0, 1/2; -3/4, 0"

   # Lean matrix notation
   lake exe lean_gaussianelimination "!![0, 1; 1, 0]"

   # Read multiple matrices from a file or stdin
   lake exe lean_gaussianelimination --file script/sample_matrices.txt
   ```

6. **Run the Fuzz Test Framework (`script/`)**:
   ```bash
   # Run default fuzz suite (deterministic edge cases + 200 random matrices)
   ./script/run_fuzz.sh

   # Customize test count, maximum matrix size, and seed
   ./script/run_fuzz.sh --num-tests 500 --max-size 7 --seed 42

   # Run and oracle-verify custom matrices via the test harness
   ./script/run_fuzz.sh --matrix "[[0, 2, 3], [4, 5, 6], [7, 8, 10]]"
   ./script/run_fuzz.sh --file script/sample_matrices.txt
   ```

### Expected Output

```
=== Verified Gaussian Elimination ===

────────────────────────────────────
2×2 Matrix Example
────────────────────────────────────
Input Matrix:
  [1, 2]
  [3, 4]

=== Gaussian Elimination Trace ===
Step 1: R1 ← R1 + (-3) * R0
Step 2: C1 ← C1 + (-2) * C0

=== Final Diagonal ===
D[0] = 1
D[1] = -2

Final Matrix:
  [1, 0]
  [0, -2]

... (more examples for 3×3, 4×4, 5×5 matrices)
```

## Using in Your Own Code

### Verified Version (Noncomputable)

```lean
import LeanGaussianelimination

open VerifiedGaussianElimination

-- Get a certificate for any matrix
noncomputable example : GaussCert (n := Fin 3) (K := ℚ) !![1, 2, 3; 4, 5, 6; 7, 8, 10] :=
  gaussianElim !![1, 2, 3; 4, 5, 6; 7, 8, 10]

-- The certificate contains a proof!
#check @gaussianElim_spec
-- ∀ M, transvecProd (gaussianElim M).L * M * transvecProd (gaussianElim M).L' 
--      = Matrix.diagonal (gaussianElim M).D
```

### Executable Version (With Trace)

```lean
import LeanGaussianelimination.Computable

open VerifiedGaussianElimination.Computable

-- Run on any size matrix
def myExample : IO Unit := do
  let M : Matrix (Fin 4) (Fin 4) ℚ := !![1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12; 13, 14, 15, 17]
  runGaussianElim M
```

## Key Concepts for Lean Beginners

### What is Lean?

Lean is a **theorem prover** and **programming language**. It can:
- Prove mathematical theorems with machine-checked proofs
- Run actual programs
- Combine proofs with code for verified software

### What is Mathlib?

[Mathlib](https://github.com/leanprover-community/mathlib4) is a comprehensive library of formalized mathematics for Lean 4. This project uses Mathlib's:
- `Matrix` type for matrices
- `TransvectionStruct` for elementary operations
- Theorems about Gaussian elimination

### Computable vs Noncomputable

- **`noncomputable def`**: Uses classical logic (existence proofs). Proves things exist but can't compute actual values.
- **`def`**: Fully computable. Can execute and produce concrete results.

This project has both:
- `gaussianElim` (noncomputable) - Proves correctness using Mathlib theorems
- `gaussianElimWithTrace` (computable) - Actually computes and shows the steps

## Supported Features

| Feature | Status |
|---------|--------|
| Arbitrary matrix size (n×n) | ✅ |
| Rational numbers (ℚ) | ✅ |
| Step-by-step trace | ✅ |
| Verified correctness | ✅ |
| Singular matrices | ✅ |
| Any field type | ✅ |

## Further Reading

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

## License

MIT License