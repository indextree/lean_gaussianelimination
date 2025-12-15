import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Rat.Lemmas

open scoped Matrix

namespace VerifiedGaussianElimination.Computable

/-!
# Computable Gaussian Elimination with Trace

This module provides a computable implementation of Gaussian elimination
that can output the sequence of elementary operations performed.
-/

variable {n : ℕ}

/-- An elementary row/column operation -/
inductive ElemOp (n : ℕ) (K : Type*) where
  | addRow (i j : Fin n) (c : K) (h : i ≠ j)    -- Rᵢ ← Rᵢ + c * Rⱼ
  | addCol (i j : Fin n) (c : K) (h : i ≠ j)    -- Cᵢ ← Cᵢ + c * Cⱼ
  deriving Repr

/-- Convert an ElemOp to a human-readable string -/
def ElemOp.toString [Repr K] : ElemOp n K → String
  | .addRow i j c _ => s!"R{i.val} ← R{i.val} + ({repr c}) * R{j.val}"
  | .addCol i j c _ => s!"C{i.val} ← C{i.val} + ({repr c}) * C{j.val}"

/-- Result of Gaussian elimination with full trace -/
structure GaussTrace (n : ℕ) (K : Type*) where
  ops : List (ElemOp n K)           -- sequence of operations
  diagonal : Fin n → K              -- resulting diagonal
  finalMatrix : Matrix (Fin n) (Fin n) K  -- the diagonal matrix

/-- Update a column of a matrix -/
def Matrix.updateCol (M : Matrix (Fin n) (Fin n) K) (j : Fin n) (f : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun i k => if k = j then f i else M i k

/-- Apply an elementary operation to a matrix -/
def applyOp [Ring K] (M : Matrix (Fin n) (Fin n) K) : ElemOp n K → Matrix (Fin n) (Fin n) K
  | .addRow i j c _ => M.updateRow i (M i + c • M j)
  | .addCol i j c _ => Matrix.updateCol M i (fun k => M k i + c * M k j)

/-- Apply a list of operations to a matrix -/
def applyOps [Ring K] (M : Matrix (Fin n) (Fin n) K) (ops : List (ElemOp n K)) : Matrix (Fin n) (Fin n) K :=
  ops.foldl applyOp M

/-- Find the first non-zero entry in column j at or below row start -/
def findPivot [DecidableEq K] [Zero K] (M : Matrix (Fin n) (Fin n) K) (j : Fin n) (start : Fin n) : Option (Fin n) :=
  (List.finRange n).filter (fun i => i.val ≥ start.val ∧ M i j ≠ 0) |>.head?

/-- Eliminate entry at (i, j) using pivot at (pivotRow, j) -/
def eliminateEntry [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (i pivotRow j : Fin n) (hne : i ≠ pivotRow) : ElemOp n K × Matrix (Fin n) (Fin n) K :=
  let c := -(M i j) / (M pivotRow j)
  let op := ElemOp.addRow i pivotRow c hne
  (op, applyOp M op)

/-- Eliminate all entries in column j except the pivot -/
def eliminateColumn [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (pivotRow j : Fin n) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  let rows := (List.finRange n).filter (fun i => i ≠ pivotRow ∧ M i j ≠ 0)
  rows.foldl (fun (ops, mat) i =>
    if h : i ≠ pivotRow then
      let (op, mat') := eliminateEntry mat i pivotRow j h
      (ops ++ [op], mat')
    else (ops, mat)
  ) ([], M)

/-- Eliminate all entries in row i except the pivot -/
def eliminateRow [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (i pivotCol : Fin n) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  let cols := (List.finRange n).filter (fun j => j ≠ pivotCol ∧ M i j ≠ 0)
  cols.foldl (fun (ops, mat) j =>
    if h : j ≠ pivotCol then
      let c := -(mat i j) / (mat i pivotCol)
      let op := ElemOp.addCol j pivotCol c h
      (ops ++ [op], applyOp mat op)
    else (ops, mat)
  ) ([], M)

/-- Main Gaussian elimination loop -/
partial def gaussElimLoop [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (k : ℕ) (ops : List (ElemOp n K)) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  if hk : k < n then
    let kFin : Fin n := ⟨k, hk⟩
    match findPivot M kFin kFin with
    | none => gaussElimLoop M (k + 1) ops  -- no pivot, skip column
    | some pivotRow =>
      -- Eliminate column entries
      let (colOps, M') := eliminateColumn M pivotRow kFin
      -- Eliminate row entries
      let (rowOps, M'') := eliminateRow M' kFin kFin
      gaussElimLoop M'' (k + 1) (ops ++ colOps ++ rowOps)
  else (ops, M)

/-- Computable Gaussian elimination with trace -/
def gaussianElimWithTrace [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K) : GaussTrace n K :=
  let (ops, finalMat) := gaussElimLoop M 0 []
  { ops := ops
    diagonal := fun i => finalMat i i
    finalMatrix := finalMat }

/-- Print the trace of operations -/
def printTrace [Repr K] (trace : GaussTrace n K) : IO Unit := do
  IO.println "=== Gaussian Elimination Trace ==="
  let mut idx := 1
  for op in trace.ops do
    IO.println s!"Step {idx}: {op.toString}"
    idx := idx + 1
  IO.println "\n=== Final Diagonal ==="
  for i in List.finRange n do
    IO.println s!"D[{i.val}] = {repr (trace.diagonal i)}"

/-- Print a matrix row by row -/
def printMatrix [Repr K] (M : Matrix (Fin n) (Fin n) K) (name : String := "Matrix") : IO Unit := do
  IO.println s!"{name}:"
  for i in List.finRange n do
    let row := (List.finRange n).map (fun j => toString (repr (M i j)))
    IO.println s!"  [{String.intercalate ", " row}]"

/-- Run Gaussian elimination on any matrix and print the trace -/
def runGaussianElim [Field K] [DecidableEq K] [Repr K] (M : Matrix (Fin n) (Fin n) K) : IO Unit := do
  printMatrix M "Input Matrix"
  IO.println ""

  let trace := gaussianElimWithTrace M
  printTrace trace

  IO.println ""
  printMatrix trace.finalMatrix "Final Matrix"

/-- Example: Run on a concrete 3x3 matrix over ℚ -/
def exampleRun : IO Unit := do
  -- Define a 3x3 matrix over ℚ
  let M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, 3; 4, 5, 6; 7, 8, 10]
  runGaussianElim M

/-- Example: Run on a 2x2 matrix -/
def example2x2 : IO Unit := do
  let M : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
  runGaussianElim M

/-- Example: Run on a 4x4 matrix -/
def example4x4 : IO Unit := do
  let M : Matrix (Fin 4) (Fin 4) ℚ := !![1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12; 13, 14, 15, 17]
  runGaussianElim M

/-- Example: Run on a 5x5 matrix -/
def example5x5 : IO Unit := do
  let M : Matrix (Fin 5) (Fin 5) ℚ := ![
    ![1, 2, 3, 4, 5],
    ![6, 7, 8, 9, 10],
    ![11, 12, 13, 14, 15],
    ![16, 17, 18, 19, 20],
    ![21, 22, 23, 24, 26]
  ]
  runGaussianElim M

end VerifiedGaussianElimination.Computable
