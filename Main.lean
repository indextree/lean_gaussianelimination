import LeanGaussianelimination
import LeanGaussianelimination.Computable

open VerifiedGaussianElimination
open VerifiedGaussianElimination.Computable

-- Example: Verify Gaussian elimination on a 2x2 matrix over ℚ
noncomputable example : GaussCert (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianElim !![1, 2; 3, 4]

-- The theorem states that for ANY matrix M:
-- there exist transvections L, L' and diagonal D such that
-- (∏L) * M * (∏L') = diagonal D
#check @gaussianElim_spec

-- Alternative factorization form: M = (∏L) * diagonal D * (∏L')
noncomputable example : GaussFactor (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianFactor !![1, 2; 3, 4]

def main : IO Unit := do
  IO.println "=== Verified Gaussian Elimination ==="
  IO.println ""

  IO.println "────────────────────────────────────"
  IO.println "2×2 Matrix Example"
  IO.println "────────────────────────────────────"
  example2x2
  IO.println ""

  IO.println "────────────────────────────────────"
  IO.println "3×3 Matrix Example"
  IO.println "────────────────────────────────────"
  exampleRun
  IO.println ""

  IO.println "────────────────────────────────────"
  IO.println "4×4 Matrix Example"
  IO.println "────────────────────────────────────"
  example4x4
  IO.println ""

  IO.println "────────────────────────────────────"
  IO.println "5×5 Matrix Example"
  IO.println "────────────────────────────────────"
  example5x5
