#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/static_audit.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: lake/Lean 4.35.0 is not installed. No build status awarded.' >&2
  exit 2
fi
mkdir -p .local-replay
lake --version | tee .local-replay/lake_version.txt
lean --version | tee .local-replay/lean_version.txt
lake exe cache get 2>&1 | tee .local-replay/mathlib_cache.log
lake build RML.Fourier.Vaaler.Toolkit 2>&1 | tee .local-replay/full_build.log
for f in examples/*.lean; do
  base="$(basename "$f" .lean)"
  lake env lean "$f" 2>&1 | tee ".local-replay/${base}.log"
done
echo 'LEAN REPLAY COMMANDS FINISHED. Inspect axiom logs and independently rerun before release.'
