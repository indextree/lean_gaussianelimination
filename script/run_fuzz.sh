#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

if [[ ! -x ".lake/build/bin/lean_gaussianelimination" ]]; then
  echo "[*] Building lean_gaussianelimination..."
  lake build
fi

exec python3 "$REPO_ROOT/script/fuzz_test.py" "$@"
