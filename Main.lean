import LeanGaussianelimination.Computable
import LeanGaussianelimination

open VerifiedGaussianElimination
open VerifiedGaussianElimination.Computable

-- Example: Verify Gaussian elimination on a 2x2 matrix over ℚ (noncomputable Mathlib witness)
noncomputable example : GaussCert (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianElim !![1, 2; 3, 4]

-- Computable verified certificate directly from `gaussianElimWithTrace`:
example : GaussCert (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianElimComputable !![1, 2; 3, 4]

-- Computable verified certificate when M[0,0] = 0 (requires pivot row change):
example : GaussCert (n := Fin 3) (K := ℚ) !![0, 2, 3; 4, 5, 6; 7, 8, 10] :=
  gaussianElimComputable !![0, 2, 3; 4, 5, 6; 7, 8, 10]

-- The theorem states that for ANY matrix M:
-- there exist transvections L, L' and diagonal D such that
-- (∏L) * M * (∏L') = diagonal D
#check @gaussianElim_spec
#check @gaussianElimWithTrace_spec

-- Alternative factorization form: M = (∏L) * diagonal D * (∏L')
noncomputable example : GaussFactor (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianFactor !![1, 2; 3, 4]

example : GaussFactor (n := Fin 2) (K := ℚ) !![1, 2; 3, 4] :=
  gaussianFactorComputable !![1, 2; 3, 4]

def runDefaultExamples : IO Unit := do
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
  IO.println "3×3 Matrix Example (Pivot Row Change)"
  IO.println "────────────────────────────────────"
  examplePivotSwap
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

def printHelp : IO Unit := do
  IO.println "Usage: lake exe lean_gaussianelimination [OPTIONS] [MATRIX ...]"
  IO.println ""
  IO.println "Options:"
  IO.println "  -h, --help            Show this help message"
  IO.println "  -m, --matrix <MAT>    Run Gaussian elimination on a custom matrix string"
  IO.println "  -f, --file <PATH>     Read one or more matrices from a file"
  IO.println "  --stdin               Read matrices from standard input (one per line)"
  IO.println ""
  IO.println "Supported Matrix Formats (over ℚ, integers or fractions a/b):"
  IO.println "  • JSON / nested list: \"[[0, 2, 3], [4, 5, 6], [7, 8, 10]]\""
  IO.println "  • Semicolon rows:     \"0, 2, 3; 4, 5, 6; 7, 8, 10\""
  IO.println "  • Lean notation:      \"!![1/2, -3/4; 5, 0]\""

/-- Split batch text into individual matrix inputs.
    If the input contains `---` separators, split on `---`;
    otherwise if lines use `[` or `;` (or each line is a single-line matrix), split line-by-line. -/
def splitBatchInputs (content : String) : List String :=
  let blocks := content.splitOn "---" |>.map String.trim |>.filter (fun b => !b.isEmpty)
  if blocks.length > 1 then
    blocks
  else
    let lines := content.splitOn "\n"
      |>.map String.trim
      |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
    if lines.any (fun l => l.contains ';' || l.startsWith "[[" || l.startsWith "!![") then
      lines
    else
      [content.trim]

partial def readAllStdinLines (acc : List String) : IO (List String) := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then
    return acc.reverse
  else
    readAllStdinLines (line :: acc)

def processArgs : List String → IO Bool
  | [] => return true
  | "-h" :: _ | "--help" :: _ => do
    printHelp
    return true
  | "-m" :: mat :: rest | "--matrix" :: mat :: rest => do
    let ok ← runCustomMatrix mat
    if !ok then return false
    if !rest.isEmpty then IO.println ""
    processArgs rest
  | "-f" :: path :: rest | "--file" :: path :: rest => do
    let content ← IO.FS.readFile path
    let inputs := splitBatchInputs content
    let mut allOk := true
    let mut first := true
    for inp in inputs do
      if !first then IO.println "\n════════════════════════════════════\n"
      first := false
      let ok ← runCustomMatrix inp
      allOk := allOk && ok
    if !allOk then return false
    processArgs rest
  | "--stdin" :: rest => do
    let lines ← readAllStdinLines []
    let content := String.intercalate "\n" lines
    let inputs := splitBatchInputs content
    let mut allOk := true
    let mut first := true
    for inp in inputs do
      if !first then IO.println "\n════════════════════════════════════\n"
      first := false
      let ok ← runCustomMatrix inp
      allOk := allOk && ok
    if !allOk then return false
    processArgs rest
  | mat :: rest => do
    let ok ← runCustomMatrix mat
    if !ok then return false
    if !rest.isEmpty then IO.println "\n════════════════════════════════════\n"
    processArgs rest

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    runDefaultExamples
    return 0
  else
    let ok ← processArgs args
    return if ok then 0 else 1
