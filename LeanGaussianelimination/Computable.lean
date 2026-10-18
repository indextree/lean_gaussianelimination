import LeanGaussianelimination
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Rat.Lemmas

open scoped Matrix
open VerifiedGaussianElimination

namespace VerifiedGaussianElimination.Computable

/-!
# Computable Gaussian Elimination with Trace and Correctness Proofs

This module provides a computable implementation of Gaussian elimination (`gaussianElimWithTrace`)
that outputs the sequence of elementary row/column operations performed, together with formal
correctness proofs connecting it to `transvecProd`, `Matrix.diagonal`, `GaussCert`, and `GaussFactor`
for any general matrix over a field.
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

@[simp]
theorem applyOps_nil [Ring K] (M : Matrix (Fin n) (Fin n) K) :
    applyOps M [] = M := rfl

@[simp]
theorem applyOps_cons [Ring K] (M : Matrix (Fin n) (Fin n) K) (op : ElemOp n K) (ops : List (ElemOp n K)) :
    applyOps M (op :: ops) = applyOps (applyOp M op) ops := rfl

@[simp]
theorem applyOps_append [Ring K] (M : Matrix (Fin n) (Fin n) K) (ops₁ ops₂ : List (ElemOp n K)) :
    applyOps M (ops₁ ++ ops₂) = applyOps (applyOps M ops₁) ops₂ :=
  List.foldl_append

theorem applyOp_addRow_apply [Ring K] (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) (c : K) (h : i ≠ j) (a b : Fin n) :
    applyOp M (.addRow i j c h) a b = if a = i then M i b + c * M j b else M a b := by
  simp only [applyOp, Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem applyOp_addCol_apply [Ring K] (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) (c : K) (h : i ≠ j) (a b : Fin n) :
    applyOp M (.addCol i j c h) a b = if b = i then M a i + c * M a j else M a b :=
  rfl

/-- Find the first non-zero entry in column j at or below row start -/
def findPivot [DecidableEq K] [Zero K] (M : Matrix (Fin n) (Fin n) K) (j : Fin n) (start : Fin n) : Option (Fin n) :=
  (List.finRange n).filter (fun i => i.val ≥ start.val ∧ M i j ≠ 0) |>.head?

/-- Find the first non-zero entry in row i at or to the right of column start -/
def findRowPivot [DecidableEq K] [Zero K] (M : Matrix (Fin n) (Fin n) K) (i : Fin n) (start : Fin n) : Option (Fin n) :=
  (List.finRange n).filter (fun j => j.val ≥ start.val ∧ M i j ≠ 0) |>.head?

/-- Eliminate entry at (i, j) using pivot at (pivotRow, j) -/
def eliminateEntry [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (i pivotRow j : Fin n) (hne : i ≠ pivotRow) : ElemOp n K × Matrix (Fin n) (Fin n) K :=
  let c := -(M i j) / (M pivotRow j)
  let op := ElemOp.addRow i pivotRow c hne
  (op, applyOp M op)

/-- Step function for `eliminateColumn` -/
def elimColStep [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (i : Fin n) :
    List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  if h : i ≠ pivotRow then
    let (op, mat') := eliminateEntry acc.2 i pivotRow j h
    (acc.1 ++ [op], mat')
  else acc

/-- Eliminate all entries in column j except the pivot -/
def eliminateColumn [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (pivotRow j : Fin n) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  let rows := (List.finRange n).filter (fun i => i ≠ pivotRow ∧ M i j ≠ 0)
  rows.foldl (elimColStep pivotRow j) ([], M)

/-- Step function for `eliminateRow` -/
def elimRowStep [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (j : Fin n) :
    List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  if h : j ≠ pivotCol then
    let c := -(acc.2 i j) / (acc.2 i pivotCol)
    let op := ElemOp.addCol j pivotCol c h
    (acc.1 ++ [op], applyOp acc.2 op)
  else acc

/-- Eliminate all entries in row i except the pivot -/
def eliminateRow [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (i pivotCol : Fin n) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  let cols := (List.finRange n).filter (fun j => j ≠ pivotCol ∧ M i j ≠ 0)
  cols.foldl (elimRowStep i pivotCol) ([], M)

theorem findPivot_some [DecidableEq K] [Zero K] {M : Matrix (Fin n) (Fin n) K} {j start p : Fin n}
    (h : findPivot M j start = some p) : p.val ≥ start.val ∧ M p j ≠ 0 := by
  unfold findPivot at h
  have hmem := List.mem_of_head? h
  rw [List.mem_filter] at hmem
  exact of_decide_eq_true hmem.2

theorem findPivot_self_eq_zero_of_ne [DecidableEq K] [Zero K] {M : Matrix (Fin n) (Fin n) K}
    {j start p : Fin n} (h : findPivot M j start = some p) (hne : start ≠ p) :
    M start j = 0 := by
  by_contra hstart
  have hp_ge : p.val ≥ start.val := (findPivot_some h).1
  unfold findPivot at h
  set l := (List.finRange n).filter (fun i => decide (i.val ≥ start.val ∧ M i j ≠ 0))
  have hpw : l.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  have hmem : start ∈ l := by
    rw [List.mem_filter]
    exact ⟨List.mem_finRange start, decide_eq_true ⟨le_refl _, hstart⟩⟩
  cases hl : l with
  | nil => simp [hl] at h
  | cons hd tl =>
    simp only [hl, List.head?_cons, Option.some.injEq] at h
    subst h
    rw [hl, List.pairwise_cons] at hpw
    rw [hl, List.mem_cons] at hmem
    have hlt : hd < start := hpw.1 start (hmem.resolve_left hne)
    exact Nat.not_lt.mpr hp_ge hlt

theorem findPivot_none [DecidableEq K] [Zero K] {M : Matrix (Fin n) (Fin n) K} {j start : Fin n}
    (h : findPivot M j start = none) (i : Fin n) (hi : i.val ≥ start.val) : M i j = 0 := by
  unfold findPivot at h
  rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at h
  have hnot := h i (List.mem_finRange i)
  rw [decide_eq_true_eq, not_and, not_ne_iff] at hnot
  exact hnot hi

theorem findRowPivot_some [DecidableEq K] [Zero K] {M : Matrix (Fin n) (Fin n) K} {i start p : Fin n}
    (h : findRowPivot M i start = some p) : p.val ≥ start.val ∧ M i p ≠ 0 := by
  unfold findRowPivot at h
  have hmem := List.mem_of_head? h
  rw [List.mem_filter] at hmem
  exact of_decide_eq_true hmem.2

theorem findRowPivot_none [DecidableEq K] [Zero K] {M : Matrix (Fin n) (Fin n) K} {i start : Fin n}
    (h : findRowPivot M i start = none) (j : Fin n) (hj : j.val ≥ start.val) : M i j = 0 := by
  unfold findRowPivot at h
  rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at h
  have hnot := h j (List.mem_finRange j)
  rw [decide_eq_true_eq, not_and, not_ne_iff] at hnot
  exact hnot hj

/-- Main Gaussian elimination loop -/
def gaussElimLoop [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K)
    (k : ℕ) (ops : List (ElemOp n K)) : List (ElemOp n K) × Matrix (Fin n) (Fin n) K :=
  if hk : k < n then
    let kFin : Fin n := ⟨k, hk⟩
    match hpiv : findPivot M kFin kFin with
    | none =>
      match hrow : findRowPivot M kFin kFin with
      | none => gaussElimLoop M (k + 1) ops  -- row and column are already zero
      | some pivotCol =>
        have hkk : M kFin kFin = 0 := findPivot_none hpiv kFin (le_refl _)
        have hne : kFin ≠ pivotCol := fun heq => (findRowPivot_some hrow).2 (heq ▸ hkk)
        -- Move non-zero entry in row kFin into (kFin, kFin) via column operation
        let prepOp := ElemOp.addCol kFin pivotCol 1 hne
        let M0 := applyOp M prepOp
        let (colOps, M') := eliminateColumn M0 kFin kFin
        let (rowOps, M'') := eliminateRow M' kFin kFin
        gaussElimLoop M'' (k + 1) (ops ++ [prepOp] ++ colOps ++ rowOps)
    | some pivotRow =>
      if hne : kFin ≠ pivotRow then
        -- Pivot found in a different row: add pivotRow to kFin so M0[kFin, kFin] ≠ 0
        let prepOp := ElemOp.addRow kFin pivotRow 1 hne
        let M0 := applyOp M prepOp
        -- Eliminate column entries using kFin as pivot row
        let (colOps, M') := eliminateColumn M0 kFin kFin
        -- Eliminate row entries using kFin as pivot column
        let (rowOps, M'') := eliminateRow M' kFin kFin
        gaussElimLoop M'' (k + 1) (ops ++ [prepOp] ++ colOps ++ rowOps)
      else
        -- Pivot is already at (kFin, kFin)
        let (colOps, M') := eliminateColumn M kFin kFin
        let (rowOps, M'') := eliminateRow M' kFin kFin
        gaussElimLoop M'' (k + 1) (ops ++ colOps ++ rowOps)
  else (ops, M)
termination_by n - k

/-- Computable Gaussian elimination with trace -/
def gaussianElimWithTrace [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K) : GaussTrace n K :=
  let (ops, finalMat) := gaussElimLoop M 0 []
  { ops := ops
    diagonal := fun i => finalMat i i
    finalMatrix := finalMat }

/-!
## Formal Correctness Proofs for `gaussianElimWithTrace`
-/

/-- Invariant: all off-diagonal entries in the first `k` rows and `k` columns are zero. -/
def IsPartiallyDiagonal [Zero K] (M : Matrix (Fin n) (Fin n) K) (k : ℕ) : Prop :=
  ∀ i j : Fin n, (i.val < k ∨ j.val < k) → i ≠ j → M i j = 0

theorem isPartiallyDiagonal_zero [Zero K] (M : Matrix (Fin n) (Fin n) K) :
    IsPartiallyDiagonal M 0 := by
  intro i j h
  rcases h with h | h <;> exact False.elim (Nat.not_lt_zero _ h)

theorem eq_diagonal_of_isPartiallyDiagonal [Zero K] {M : Matrix (Fin n) (Fin n) K}
    (h : IsPartiallyDiagonal M n) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact h i j (Or.inl i.isLt) hij

/-! ### Correctness of `eliminateColumn` -/

theorem elimColStep_applyOps [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (M₀ : Matrix (Fin n) (Fin n) K) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (i : Fin n) (hacc : applyOps M₀ acc.1 = acc.2) :
    applyOps M₀ (elimColStep pivotRow j acc i).1 = (elimColStep pivotRow j acc i).2 := by
  unfold elimColStep
  split_ifs with h
  · simp [eliminateEntry, hacc]
  · exact hacc

theorem foldl_elimColStep_applyOps [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (l : List (Fin n)) (M₀ : Matrix (Fin n) (Fin n) K)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hacc : applyOps M₀ acc.1 = acc.2) :
    applyOps M₀ (l.foldl (elimColStep pivotRow j) acc).1 =
      (l.foldl (elimColStep pivotRow j) acc).2 := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons i rest ih =>
    exact ih (elimColStep pivotRow j acc i) (elimColStep_applyOps pivotRow j M₀ acc i hacc)

theorem eliminateColumn_applyOps [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) (pivotRow j : Fin n) :
    applyOps M (eliminateColumn M pivotRow j).1 = (eliminateColumn M pivotRow j).2 :=
  foldl_elimColStep_applyOps pivotRow j _ M ([], M) rfl

theorem elimColStep_pivotRow [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (r b : Fin n) :
    (elimColStep pivotRow j acc r).2 pivotRow b = acc.2 pivotRow b := by
  unfold elimColStep
  split_ifs with h
  · simp [eliminateEntry, applyOp_addRow_apply, Ne.symm h]
  · rfl

theorem foldl_elimColStep_pivotRow [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (b : Fin n) :
    (l.foldl (elimColStep pivotRow j) acc).2 pivotRow b = acc.2 pivotRow b := by
  induction l generalizing acc with
  | nil => rfl
  | cons r rest ih =>
    rw [List.foldl_cons, ih, elimColStep_pivotRow]

theorem eliminateColumn_pivotRow [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) (pivotRow j b : Fin n) :
    (eliminateColumn M pivotRow j).2 pivotRow b = M pivotRow b :=
  foldl_elimColStep_pivotRow pivotRow j _ ([], M) b

theorem elimColStep_self [Field K] [DecidableEq K] {pivotRow j i : Fin n}
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hi : i ≠ pivotRow) (hpiv : acc.2 pivotRow j ≠ 0) :
    (elimColStep pivotRow j acc i).2 i j = 0 := by
  unfold elimColStep
  rw [dif_pos hi]
  simp only [eliminateEntry, applyOp_addRow_apply, ↓reduceIte]
  rw [neg_div, neg_mul, div_mul_cancel₀ _ hpiv, add_neg_cancel]

theorem elimColStep_of_ne [Field K] [DecidableEq K] (pivotRow j : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) {r i : Fin n} (hri : i ≠ r) (b : Fin n) :
    (elimColStep pivotRow j acc r).2 i b = acc.2 i b := by
  unfold elimColStep
  split_ifs with h
  · simp [eliminateEntry, applyOp_addRow_apply, hri]
  · rfl

theorem foldl_elimColStep_zero_of_zero [Field K] [DecidableEq K] {pivotRow j i : Fin n}
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hi : i ≠ pivotRow) (hpiv : acc.2 pivotRow j ≠ 0) (hzero : acc.2 i j = 0) :
    (l.foldl (elimColStep pivotRow j) acc).2 i j = 0 := by
  induction l generalizing acc with
  | nil => exact hzero
  | cons r rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [elimColStep_pivotRow]; exact hpiv
    · by_cases hri : i = r
      · subst hri; exact elimColStep_self acc hi hpiv
      · rw [elimColStep_of_ne pivotRow j acc hri j]; exact hzero

theorem foldl_elimColStep_zero_of_mem [Field K] [DecidableEq K] {pivotRow j i : Fin n}
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hi : i ≠ pivotRow) (hpiv : acc.2 pivotRow j ≠ 0) (hmem : i ∈ l) :
    (l.foldl (elimColStep pivotRow j) acc).2 i j = 0 := by
  induction l generalizing acc with
  | nil => contradiction
  | cons r rest ih =>
    rw [List.foldl_cons]
    have hpiv' : (elimColStep pivotRow j acc r).2 pivotRow j = acc.2 pivotRow j :=
      elimColStep_pivotRow pivotRow j acc r j
    by_cases hri : i = r
    · subst hri
      exact foldl_elimColStep_zero_of_zero rest _ hi (hpiv' ▸ hpiv) (elimColStep_self acc hi hpiv)
    · rw [List.mem_cons] at hmem
      exact ih _ (hpiv' ▸ hpiv) (hmem.resolve_left hri)

theorem eliminateColumn_zero_of_ne [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) {pivotRow j i : Fin n}
    (hpiv : M pivotRow j ≠ 0) (hi : i ≠ pivotRow) :
    (eliminateColumn M pivotRow j).2 i j = 0 := by
  unfold eliminateColumn
  by_cases hij : M i j = 0
  · exact foldl_elimColStep_zero_of_zero _ ([], M) hi hpiv hij
  · apply foldl_elimColStep_zero_of_mem _ ([], M) hi hpiv
    rw [List.mem_filter]
    exact ⟨List.mem_finRange i, decide_eq_true ⟨hi, hij⟩⟩

theorem elimColStep_isPartiallyDiagonal [Field K] [DecidableEq K]
    {k : ℕ} (hk : k < n) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (r : Fin n)
    (hdiag : IsPartiallyDiagonal acc.2 k) :
    IsPartiallyDiagonal (elimColStep ⟨k, hk⟩ ⟨k, hk⟩ acc r).2 k := by
  unfold elimColStep
  split_ifs with h
  · intro a b hab_lt hab
    simp only [eliminateEntry, applyOp_addRow_apply]
    split_ifs with har
    · subst har
      by_cases ha_lt : a.val < k
      · have hak : acc.2 a ⟨k, hk⟩ = 0 := hdiag a ⟨k, hk⟩ (Or.inl ha_lt) h
        have hab0 : acc.2 a b = 0 := hdiag a b (Or.inl ha_lt) hab
        simp [hak, hab0]
      · have hb_lt : b.val < k := hab_lt.resolve_left ha_lt
        have hab0 : acc.2 a b = 0 := hdiag a b (Or.inr hb_lt) hab
        have hkb : (⟨k, hk⟩ : Fin n) ≠ b := fun heq => Nat.ne_of_gt hb_lt (congrArg Fin.val heq)
        have hkb0 : acc.2 ⟨k, hk⟩ b = 0 := hdiag ⟨k, hk⟩ b (Or.inr hb_lt) hkb
        simp [hab0, hkb0]
    · exact hdiag a b hab_lt hab
  · exact hdiag

theorem foldl_elimColStep_isPartiallyDiagonal [Field K] [DecidableEq K]
    {k : ℕ} (hk : k < n) (l : List (Fin n))
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hdiag : IsPartiallyDiagonal acc.2 k) :
    IsPartiallyDiagonal (l.foldl (elimColStep ⟨k, hk⟩ ⟨k, hk⟩) acc).2 k := by
  induction l generalizing acc with
  | nil => exact hdiag
  | cons r rest ih =>
    exact ih _ (elimColStep_isPartiallyDiagonal hk acc r hdiag)

theorem eliminateColumn_isPartiallyDiagonal [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k < n)
    (hdiag : IsPartiallyDiagonal M k) :
    IsPartiallyDiagonal (eliminateColumn M ⟨k, hk⟩ ⟨k, hk⟩).2 k :=
  foldl_elimColStep_isPartiallyDiagonal hk _ ([], M) hdiag

/-! ### Correctness of `eliminateRow` -/

theorem elimRowStep_applyOps [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (M₀ : Matrix (Fin n) (Fin n) K) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (j : Fin n) (hacc : applyOps M₀ acc.1 = acc.2) :
    applyOps M₀ (elimRowStep i pivotCol acc j).1 = (elimRowStep i pivotCol acc j).2 := by
  unfold elimRowStep
  split_ifs with h
  · simp [hacc]
  · exact hacc

theorem foldl_elimRowStep_applyOps [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (l : List (Fin n)) (M₀ : Matrix (Fin n) (Fin n) K)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hacc : applyOps M₀ acc.1 = acc.2) :
    applyOps M₀ (l.foldl (elimRowStep i pivotCol) acc).1 =
      (l.foldl (elimRowStep i pivotCol) acc).2 := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons j rest ih =>
    exact ih (elimRowStep i pivotCol acc j) (elimRowStep_applyOps i pivotCol M₀ acc j hacc)

theorem eliminateRow_applyOps [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) (i pivotCol : Fin n) :
    applyOps M (eliminateRow M i pivotCol).1 = (eliminateRow M i pivotCol).2 :=
  foldl_elimRowStep_applyOps i pivotCol _ M ([], M) rfl

theorem elimRowStep_pivotCol [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (r a : Fin n) :
    (elimRowStep i pivotCol acc r).2 a pivotCol = acc.2 a pivotCol := by
  unfold elimRowStep
  split_ifs with h
  · simp [applyOp_addCol_apply, Ne.symm h]
  · rfl

theorem foldl_elimRowStep_pivotCol [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (a : Fin n) :
    (l.foldl (elimRowStep i pivotCol) acc).2 a pivotCol = acc.2 a pivotCol := by
  induction l generalizing acc with
  | nil => rfl
  | cons r rest ih =>
    rw [List.foldl_cons, ih, elimRowStep_pivotCol]

theorem elimRowStep_self [Field K] [DecidableEq K] {i pivotCol j : Fin n}
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hj : j ≠ pivotCol) (hpiv : acc.2 i pivotCol ≠ 0) :
    (elimRowStep i pivotCol acc j).2 i j = 0 := by
  unfold elimRowStep
  rw [dif_pos hj]
  simp only [applyOp_addCol_apply, ↓reduceIte]
  rw [neg_div, neg_mul, div_mul_cancel₀ _ hpiv, add_neg_cancel]

theorem elimRowStep_of_ne [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) {r j : Fin n} (hrj : j ≠ r) (a : Fin n) :
    (elimRowStep i pivotCol acc r).2 a j = acc.2 a j := by
  unfold elimRowStep
  split_ifs with h
  · simp [applyOp_addCol_apply, hrj]
  · rfl

theorem foldl_elimRowStep_zero_of_zero [Field K] [DecidableEq K] {i pivotCol j : Fin n}
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hj : j ≠ pivotCol) (hpiv : acc.2 i pivotCol ≠ 0) (hzero : acc.2 i j = 0) :
    (l.foldl (elimRowStep i pivotCol) acc).2 i j = 0 := by
  induction l generalizing acc with
  | nil => exact hzero
  | cons r rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [elimRowStep_pivotCol]; exact hpiv
    · by_cases hrj : j = r
      · subst hrj; exact elimRowStep_self acc hj hpiv
      · rw [elimRowStep_of_ne i pivotCol acc hrj i]; exact hzero

theorem foldl_elimRowStep_zero_of_mem [Field K] [DecidableEq K] {i pivotCol j : Fin n}
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    (hj : j ≠ pivotCol) (hpiv : acc.2 i pivotCol ≠ 0) (hmem : j ∈ l) :
    (l.foldl (elimRowStep i pivotCol) acc).2 i j = 0 := by
  induction l generalizing acc with
  | nil => contradiction
  | cons r rest ih =>
    rw [List.foldl_cons]
    have hpiv' : (elimRowStep i pivotCol acc r).2 i pivotCol = acc.2 i pivotCol :=
      elimRowStep_pivotCol i pivotCol acc r i
    by_cases hrj : j = r
    · subst hrj
      exact foldl_elimRowStep_zero_of_zero rest _ hj (hpiv' ▸ hpiv) (elimRowStep_self acc hj hpiv)
    · rw [List.mem_cons] at hmem
      exact ih _ (hpiv' ▸ hpiv) (hmem.resolve_left hrj)

theorem eliminateRow_zero_of_ne [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) {i pivotCol j : Fin n}
    (hpiv : M i pivotCol ≠ 0) (hj : j ≠ pivotCol) :
    (eliminateRow M i pivotCol).2 i j = 0 := by
  unfold eliminateRow
  by_cases hij : M i j = 0
  · exact foldl_elimRowStep_zero_of_zero _ ([], M) hj hpiv hij
  · apply foldl_elimRowStep_zero_of_mem _ ([], M) hj hpiv
    rw [List.mem_filter]
    exact ⟨List.mem_finRange j, decide_eq_true ⟨hj, hij⟩⟩

theorem elimRowStep_row_of_col_zero [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K) (r : Fin n)
    {a : Fin n} (hcol : acc.2 a pivotCol = 0) (b : Fin n) :
    (elimRowStep i pivotCol acc r).2 a b = acc.2 a b := by
  unfold elimRowStep
  split_ifs with h
  · simp only [applyOp_addCol_apply, hcol, mul_zero, add_zero]
    split_ifs with hbr
    · subst hbr; rfl
    · rfl
  · rfl

theorem foldl_elimRowStep_row_of_col_zero [Field K] [DecidableEq K] (i pivotCol : Fin n)
    (l : List (Fin n)) (acc : List (ElemOp n K) × Matrix (Fin n) (Fin n) K)
    {a : Fin n} (hcol : acc.2 a pivotCol = 0) (b : Fin n) :
    (l.foldl (elimRowStep i pivotCol) acc).2 a b = acc.2 a b := by
  induction l generalizing acc with
  | nil => rfl
  | cons r rest ih =>
    rw [List.foldl_cons, ih]
    · exact elimRowStep_row_of_col_zero i pivotCol acc r hcol b
    · rw [elimRowStep_pivotCol]; exact hcol

theorem eliminateRow_row_of_col_zero [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) (i pivotCol : Fin n)
    {a : Fin n} (hcol : M a pivotCol = 0) (b : Fin n) :
    (eliminateRow M i pivotCol).2 a b = M a b :=
  foldl_elimRowStep_row_of_col_zero i pivotCol _ ([], M) hcol b

/-! ### Combined Column + Row Elimination Step -/

theorem eliminateColumn_eliminateRow_step [Field K] [DecidableEq K]
    (M0 : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k < n)
    (hdiag : IsPartiallyDiagonal M0 k) (hpiv : M0 ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0) :
    applyOps M0 ((eliminateColumn M0 ⟨k, hk⟩ ⟨k, hk⟩).1 ++
      (eliminateRow (eliminateColumn M0 ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).1) =
      (eliminateRow (eliminateColumn M0 ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).2 ∧
    IsPartiallyDiagonal
      (eliminateRow (eliminateColumn M0 ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).2 (k + 1) := by
  let kFin : Fin n := ⟨k, hk⟩
  set colRes := eliminateColumn M0 kFin kFin
  set rowRes := eliminateRow colRes.2 kFin kFin
  have h_ops : applyOps M0 (colRes.1 ++ rowRes.1) = rowRes.2 := by
    rw [applyOps_append, eliminateColumn_applyOps, eliminateRow_applyOps]
  refine ⟨h_ops, ?_⟩
  have hM'_diag : IsPartiallyDiagonal colRes.2 k :=
    eliminateColumn_isPartiallyDiagonal M0 hk hdiag
  have hM'_piv : colRes.2 kFin kFin ≠ 0 := by
    rw [eliminateColumn_pivotRow]; exact hpiv
  have hM'_col : ∀ i : Fin n, i ≠ kFin → colRes.2 i kFin = 0 :=
    fun i hi => eliminateColumn_zero_of_ne M0 hpiv hi
  intro a b hab_lt hab
  by_cases ha : a = kFin
  · subst ha
    have hb : b ≠ kFin := hab.symm
    exact eliminateRow_zero_of_ne colRes.2 hM'_piv hb
  · rw [eliminateRow_row_of_col_zero colRes.2 kFin kFin (hM'_col a ha) b]
    by_cases hb : b = kFin
    · subst hb
      exact hM'_col a ha
    · have ha_ne : a.val ≠ k := fun heq => ha (Fin.ext heq)
      have hb_ne : b.val ≠ k := fun heq => hb (Fin.ext heq)
      have hab_lt' : a.val < k ∨ b.val < k := by omega
      exact hM'_diag a b hab_lt' hab

/-! ### Preparatory Row/Column Operations Preserve `IsPartiallyDiagonal` -/

theorem addRow_prep_spec [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k < n) {pivotRow : Fin n}
    (hdiag : IsPartiallyDiagonal M k)
    (hkk : M ⟨k, hk⟩ ⟨k, hk⟩ = 0)
    (hpiv_ge : pivotRow.val ≥ k) (hpiv_ne : M pivotRow ⟨k, hk⟩ ≠ 0)
    (hne : (⟨k, hk⟩ : Fin n) ≠ pivotRow) :
    IsPartiallyDiagonal (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) k ∧
      (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro a b hab_lt hab
    simp only [applyOp_addRow_apply]
    split_ifs with ha
    · subst ha
      have hb_lt : b.val < k := hab_lt.resolve_left (Nat.lt_irrefl k)
      have hkb : M ⟨k, hk⟩ b = 0 := hdiag ⟨k, hk⟩ b (Or.inr hb_lt) hab
      have hpiv_b : pivotRow ≠ b := fun heq => Nat.not_lt.mpr hpiv_ge (heq ▸ hb_lt)
      have hpb : M pivotRow b = 0 := hdiag pivotRow b (Or.inr hb_lt) hpiv_b
      simp [hkb, hpb]
    · exact hdiag a b hab_lt hab
  · simp [applyOp_addRow_apply, hkk, hpiv_ne]

theorem addCol_prep_spec [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k < n) {pivotCol : Fin n}
    (hdiag : IsPartiallyDiagonal M k)
    (hkk : M ⟨k, hk⟩ ⟨k, hk⟩ = 0)
    (hpiv_ge : pivotCol.val ≥ k) (hpiv_ne : M ⟨k, hk⟩ pivotCol ≠ 0)
    (hne : (⟨k, hk⟩ : Fin n) ≠ pivotCol) :
    IsPartiallyDiagonal (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) k ∧
      (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro a b hab_lt hab
    simp only [applyOp_addCol_apply]
    split_ifs with hb
    · subst hb
      have ha_lt : a.val < k := hab_lt.resolve_right (Nat.lt_irrefl k)
      have hak : M a ⟨k, hk⟩ = 0 := hdiag a ⟨k, hk⟩ (Or.inl ha_lt) hab
      have ha_piv : a ≠ pivotCol := fun heq => Nat.not_lt.mpr hpiv_ge (heq ▸ ha_lt)
      have hap : M a pivotCol = 0 := hdiag a pivotCol (Or.inl ha_lt) ha_piv
      simp [hak, hap]
    · exact hdiag a b hab_lt hab
  · simp [applyOp_addCol_apply, hkk, hpiv_ne]

/-! ### Main Loop Invariant and Correctness Theorems -/

theorem gaussElimLoop_spec [Field K] [DecidableEq K]
    (M₀ M : Matrix (Fin n) (Fin n) K) (k : ℕ) (ops : List (ElemOp n K))
    (hacc : applyOps M₀ ops = M) (hdiag : IsPartiallyDiagonal M k) :
    applyOps M₀ (gaussElimLoop M k ops).1 = (gaussElimLoop M k ops).2 ∧
      IsPartiallyDiagonal (gaussElimLoop M k ops).2 n := by
  rw [gaussElimLoop]
  split_ifs with hk
  · dsimp only
    split
    · next hpiv =>
      split
      · next hrow =>
        have hdiag_next : IsPartiallyDiagonal M (k + 1) := by
          intro a b hab_lt hab
          by_cases ha : a = ⟨k, hk⟩
          · subst ha
            by_cases hb_lt : b.val < k
            · exact hdiag ⟨k, hk⟩ b (Or.inr hb_lt) hab
            · exact findRowPivot_none hrow b (Nat.le_of_not_lt hb_lt)
          · by_cases hb : b = ⟨k, hk⟩
            · subst hb
              by_cases ha_lt : a.val < k
              · exact hdiag a ⟨k, hk⟩ (Or.inl ha_lt) hab
              · exact findPivot_none hpiv a (Nat.le_of_not_lt ha_lt)
            · have ha_ne : a.val ≠ k := fun heq => ha (Fin.ext heq)
              have hb_ne : b.val ≠ k := fun heq => hb (Fin.ext heq)
              have hab_lt' : a.val < k ∨ b.val < k := by omega
              exact hdiag a b hab_lt' hab
        exact gaussElimLoop_spec M₀ M (k + 1) ops hacc hdiag_next
      · next pivotCol hrow =>
        have hkk : M ⟨k, hk⟩ ⟨k, hk⟩ = 0 := findPivot_none hpiv ⟨k, hk⟩ (le_refl _)
        have hcol := findRowPivot_some hrow
        have hne : (⟨k, hk⟩ : Fin n) ≠ pivotCol := fun heq => hcol.2 (heq ▸ hkk)
        have hprep := addCol_prep_spec M hk hdiag hkk hcol.1 hcol.2 hne
        have hstep := eliminateColumn_eliminateRow_step
          (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) hk hprep.1 hprep.2
        have hacc' :
            applyOps M₀
              (ops ++ [.addCol ⟨k, hk⟩ pivotCol 1 hne] ++
                (eliminateColumn (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).1 ++
                (eliminateRow (eliminateColumn (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).1) =
              (eliminateRow (eliminateColumn (applyOp M (.addCol ⟨k, hk⟩ pivotCol 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).2 := by
          rw [List.append_assoc ops, List.append_assoc, applyOps_append, hacc,
            List.singleton_append, List.cons_append, applyOps_cons, hstep.1]
        exact gaussElimLoop_spec M₀ _ (k + 1) _ hacc' hstep.2
    · next pivotRow hpiv =>
      split_ifs with hne
      · have hpiv_spec := findPivot_some hpiv
        have hkk : M ⟨k, hk⟩ ⟨k, hk⟩ = 0 := findPivot_self_eq_zero_of_ne hpiv hne
        have hprep := addRow_prep_spec M hk hdiag hkk hpiv_spec.1 hpiv_spec.2 hne
        have hstep := eliminateColumn_eliminateRow_step
          (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) hk hprep.1 hprep.2
        have hacc' :
            applyOps M₀
              (ops ++ [.addRow ⟨k, hk⟩ pivotRow 1 hne] ++
                (eliminateColumn (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).1 ++
                (eliminateRow (eliminateColumn (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).1) =
              (eliminateRow (eliminateColumn (applyOp M (.addRow ⟨k, hk⟩ pivotRow 1 hne)) ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).2 := by
          rw [List.append_assoc ops, List.append_assoc, applyOps_append, hacc,
            List.singleton_append, List.cons_append, applyOps_cons, hstep.1]
        exact gaussElimLoop_spec M₀ _ (k + 1) _ hacc' hstep.2
      · have heq : (⟨k, hk⟩ : Fin n) = pivotRow := not_ne_iff.mp hne
        have hkk : M ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0 := heq ▸ (findPivot_some hpiv).2
        have hstep := eliminateColumn_eliminateRow_step M hk hdiag hkk
        have hacc' :
            applyOps M₀
              (ops ++ (eliminateColumn M ⟨k, hk⟩ ⟨k, hk⟩).1 ++
                (eliminateRow (eliminateColumn M ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).1) =
              (eliminateRow (eliminateColumn M ⟨k, hk⟩ ⟨k, hk⟩).2 ⟨k, hk⟩ ⟨k, hk⟩).2 := by
          rw [List.append_assoc, applyOps_append, hacc, hstep.1]
        exact gaussElimLoop_spec M₀ _ (k + 1) _ hacc' hstep.2
  · refine ⟨hacc, ?_⟩
    intro a b _ hab
    exact hdiag a b (Or.inl (Nat.lt_of_lt_of_le a.isLt (Nat.le_of_not_lt hk))) hab
termination_by n - k

/-- Applying the operations in `gaussianElimWithTrace M` to `M` yields `finalMatrix`. -/
theorem gaussianElimWithTrace_applyOps [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) :
    applyOps M (gaussianElimWithTrace M).ops = (gaussianElimWithTrace M).finalMatrix :=
  (gaussElimLoop_spec M M 0 [] rfl (isPartiallyDiagonal_zero M)).1

/-- The `finalMatrix` produced by `gaussianElimWithTrace M` is diagonal with entries `diagonal`. -/
theorem gaussianElimWithTrace_finalMatrix_eq_diagonal [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) :
    (gaussianElimWithTrace M).finalMatrix = Matrix.diagonal (gaussianElimWithTrace M).diagonal :=
  eq_diagonal_of_isPartiallyDiagonal (gaussElimLoop_spec M M 0 [] rfl (isPartiallyDiagonal_zero M)).2

/-- Applying the operations in `gaussianElimWithTrace M` reduces any matrix `M` to diagonal form. -/
theorem gaussianElimWithTrace_eq_diagonal [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) :
    applyOps M (gaussianElimWithTrace M).ops = Matrix.diagonal (gaussianElimWithTrace M).diagonal := by
  rw [gaussianElimWithTrace_applyOps, gaussianElimWithTrace_finalMatrix_eq_diagonal]

/-!
## Connection to Transvections, `GaussCert`, and `GaussFactor`
-/

theorem applyOp_addRow_eq_transvection_mul [CommRing K] (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) (c : K) (h : i ≠ j) :
    applyOp M (.addRow i j c h) = Matrix.transvection i j c * M := by
  ext a b
  rw [applyOp_addRow_apply]
  by_cases ha : a = i
  · subst ha
    simp [Matrix.transvection_mul_apply_same]
  · simp [Matrix.transvection_mul_apply_of_ne, ha]

theorem applyOp_addCol_eq_mul_transvection [CommRing K] (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) (c : K) (h : i ≠ j) :
    applyOp M (.addCol i j c h) = M * Matrix.transvection j i c := by
  ext a b
  rw [applyOp_addCol_apply]
  by_cases hb : b = i
  · subst hb
    simp [Matrix.mul_transvection_apply_same]
  · simp [Matrix.mul_transvection_apply_of_ne, hb]

/-- Extract left transvections (row operations) from a list of elementary operations. -/
def opsToLeftTransvecs : List (ElemOp n K) → List (Matrix.TransvectionStruct (Fin n) K)
  | [] => []
  | .addRow i j c h :: rest => opsToLeftTransvecs rest ++ [⟨i, j, h, c⟩]
  | .addCol _ _ _ _ :: rest => opsToLeftTransvecs rest

/-- Extract right transvections (column operations) from a list of elementary operations. -/
def opsToRightTransvecs : List (ElemOp n K) → List (Matrix.TransvectionStruct (Fin n) K)
  | [] => []
  | .addRow _ _ _ _ :: rest => opsToRightTransvecs rest
  | .addCol i j c h :: rest => ⟨j, i, h.symm, c⟩ :: opsToRightTransvecs rest

@[simp]
theorem transvecProd_nil [Field K] :
    transvecProd (n := Fin n) (K := K) [] = 1 := rfl

@[simp]
theorem transvecProd_cons [Field K] (t : Matrix.TransvectionStruct (Fin n) K)
    (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    transvecProd (t :: L) = t.toMatrix * transvecProd L := by
  simp [transvecProd]

@[simp]
theorem transvecProd_append [Field K]
    (L₁ L₂ : List (Matrix.TransvectionStruct (Fin n) K)) :
    transvecProd (L₁ ++ L₂) = transvecProd L₁ * transvecProd L₂ := by
  simp [transvecProd, List.prod_append]

/-- Multiplying by `opsToLeftTransvecs ops` on the left and `opsToRightTransvecs ops` on the right
    equals applying `ops` via `applyOps`. -/
theorem transvecProd_opsToTransvecs_eq_applyOps [Field K]
    (M : Matrix (Fin n) (Fin n) K) (ops : List (ElemOp n K)) :
    transvecProd (opsToLeftTransvecs ops) * M * transvecProd (opsToRightTransvecs ops) =
      applyOps M ops := by
  induction ops generalizing M with
  | nil => simp [opsToLeftTransvecs, opsToRightTransvecs, applyOps]
  | cons op rest ih =>
    cases op with
    | addRow i j c h =>
      simp only [opsToLeftTransvecs, opsToRightTransvecs, applyOps_cons,
        applyOp_addRow_eq_transvection_mul, ← ih]
      simp [Matrix.mul_assoc]
    | addCol i j c h =>
      simp only [opsToLeftTransvecs, opsToRightTransvecs, applyOps_cons,
        applyOp_addCol_eq_mul_transvection, ← ih]
      simp [Matrix.mul_assoc]

/-- Main correctness theorem for `gaussianElimWithTrace`:
    The transvection lists extracted from `(gaussianElimWithTrace M).ops` reduce `M`
    to `Matrix.diagonal (gaussianElimWithTrace M).diagonal`. -/
theorem gaussianElimWithTrace_spec [Field K] [DecidableEq K]
    (M : Matrix (Fin n) (Fin n) K) :
    transvecProd (opsToLeftTransvecs (gaussianElimWithTrace M).ops)
      * M
      * transvecProd (opsToRightTransvecs (gaussianElimWithTrace M).ops)
    = Matrix.diagonal (gaussianElimWithTrace M).diagonal := by
  rw [transvecProd_opsToTransvecs_eq_applyOps, gaussianElimWithTrace_eq_diagonal]

/-- Computably construct a verified `GaussCert` directly from `gaussianElimWithTrace`. -/
def gaussianElimComputable [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K) :
    GaussCert (n := Fin n) (K := K) M where
  L  := opsToLeftTransvecs (gaussianElimWithTrace M).ops
  L' := opsToRightTransvecs (gaussianElimWithTrace M).ops
  D  := (gaussianElimWithTrace M).diagonal
  h  := gaussianElimWithTrace_spec M

/-- Computably construct a verified `GaussFactor` directly from `gaussianElimWithTrace`. -/
def gaussianFactorComputable [Field K] [DecidableEq K] (M : Matrix (Fin n) (Fin n) K) :
    GaussFactor (n := Fin n) (K := K) M :=
  let cert := gaussianElimComputable M
  { L  := cert.L.reverse.map Matrix.TransvectionStruct.inv
    L' := cert.L'.reverse.map Matrix.TransvectionStruct.inv
    D  := cert.D
    h  := by
      have h := cert.h
      suffices
        M =
          (cert.L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod *
            (cert.L.map Matrix.TransvectionStruct.toMatrix).prod * M *
            ((cert.L'.map Matrix.TransvectionStruct.toMatrix).prod *
              (cert.L'.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod)
        by simpa [transvecProd, ← h, Matrix.mul_assoc]
      rw [Matrix.TransvectionStruct.reverse_inv_prod_mul_prod,
        Matrix.TransvectionStruct.prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one] }

/-!
## IO Printing and Examples
-/

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

/-- Example: Run on a 3x3 matrix where M[0,0] = 0 (requires pivot row change) -/
def examplePivotSwap : IO Unit := do
  let M : Matrix (Fin 3) (Fin 3) ℚ := !![0, 2, 3; 4, 5, 6; 7, 8, 10]
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
