import Mathlib.LinearAlgebra.Matrix.Transvection

open scoped Matrix

namespace VerifiedGaussianElimination

universe u v

variable {n : Type u} {K : Type v}
variable [Fintype n] [DecidableEq n] [Field K]

/-- Product of matrices obtained by converting `TransvectionStruct`s in a list to matrices. -/
def transvecProd (L : List (Matrix.TransvectionStruct n K)) : Matrix n n K :=
  (L.map Matrix.TransvectionStruct.toMatrix).prod

/--
A "certificate" that `M` has been reduced to a diagonal matrix via products of (left/right) transvections.

`L`  : Transvections multiplied on the left (corresponding to row operations)
`L'` : Transvections multiplied on the right (corresponding to column operations)
`D`  : Diagonal entries of the resulting diagonal matrix
`h`  : Proof that diagonalization actually holds
-/
structure GaussCert (M : Matrix n n K) : Type (max u v) where
  L  : List (Matrix.TransvectionStruct n K)
  L' : List (Matrix.TransvectionStruct n K)
  D  : n → K
  h  : transvecProd (n := n) (K := K) L * M * transvecProd (n := n) (K := K) L'
        = Matrix.diagonal D

/--
Returns a verifiable Gaussian elimination (Gaussian pivot) "result + certificate".

Note: This is `noncomputable` because it uses `Classical.choose` to extract witnesses from Mathlib's existence theorem.
-/
noncomputable def gaussianElim (M : Matrix n n K) : GaussCert (n := n) (K := K) M :=
  let h := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M := M)
  let L := Classical.choose h
  let h' := Classical.choose_spec h
  let L' := Classical.choose h'
  let h'' := Classical.choose_spec h'
  let D := Classical.choose h''
  let pf := Classical.choose_spec h''
  ⟨L, L', D, pf⟩

/-- A convenient form for directly using the certificate returned by `gaussianElim`. -/
theorem gaussianElim_spec (M : Matrix n n K) :
    transvecProd (n := n) (K := K) (gaussianElim (n := n) (K := K) M).L
      * M
      * transvecProd (n := n) (K := K) (gaussianElim (n := n) (K := K) M).L'
    =
    Matrix.diagonal (gaussianElim (n := n) (K := K) M).D :=
  (gaussianElim (n := n) (K := K) M).h

/-
(Note) Mathlib also provides a "factorization form":

  ∃ L L' D, M = (∏L) * diagonal D * (∏L')

If desired, this can also be wrapped as a certificate in the same way.
-/
structure GaussFactor (M : Matrix n n K) : Type (max u v) where
  L  : List (Matrix.TransvectionStruct n K)
  L' : List (Matrix.TransvectionStruct n K)
  D  : n → K
  h  : M
        = transvecProd (n := n) (K := K) L
          * Matrix.diagonal D
          * transvecProd (n := n) (K := K) L'

noncomputable def gaussianFactor (M : Matrix n n K) : GaussFactor (n := n) (K := K) M :=
  let h := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (M := M)
  let L := Classical.choose h
  let h' := Classical.choose_spec h
  let L' := Classical.choose h'
  let h'' := Classical.choose_spec h'
  let D := Classical.choose h''
  let pf := Classical.choose_spec h''
  ⟨L, L', D, pf⟩

end VerifiedGaussianElimination
