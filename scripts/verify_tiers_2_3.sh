#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/static_audit.py
python3 scripts/test_static_audit.py
lake --version
lean --version
lake build RML.Fourier.Vaaler.Toolkit
for p in examples/*.lean; do
  printf "Compiling consumer: %s\n" "$p"
  lake env lean "$p"
done
echo 'All toolkit imports and consumer examples passed.'
