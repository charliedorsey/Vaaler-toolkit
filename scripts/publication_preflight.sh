#!/usr/bin/env bash
# NON-MUTATING local first-publication preflight. NEVER pushes, tags or commits.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "===== PUBLICATION DRY RUN ONLY (NO PUSH) ====="
echo "Commit: $(git rev-parse HEAD)"
echo "Branch: $(git branch --show-current)"
echo "Remote: $(git remote get-url origin)"
if [[ -n "$(git status --porcelain)" ]]; then
  echo "FAIL: Uncommitted changes / untracked files; freeze the candidate first."
  git status --short
  exit 3
fi
git diff --check
test -s LICENSE
test -s NOTICE
test -s lean-toolchain
test -s lake-manifest.json
test -s .github/workflows/lean.yml
test -s .github/workflows/palomar-manual-preflight.yml
test -s comparator.json
test -s formalization.yaml
test -s Challenge.lean
test -s Solution.lean
test -s docs/provenance.md
for f in RML/Fourier/Vaaler/Internal/Analytic/FejerTriangle.lean RML/Fourier/Vaaler/Internal/Analytic/SincSquare.lean; do
  test -s "$f"
done
bad=$(git ls-files | grep -E '(^|/)(private_evidence|\.lake|\.local-replay|__pycache__)/|PROVENANCE_AND_APACHE_AUTHORIZATION_R0005|\.pem$|\.key$|\.env$' || true)
if [[ -n "$bad" ]]; then
  printf '%s\n' "$bad"
  echo 'FAIL: Private content tracked.'
  exit 4
fi
python3 scripts/check_release_docs.py
python3 scripts/static_audit.py
python3 scripts/test_static_audit.py
python3 scripts/module_migration_integrity.py
python3 scripts/test_comparator_safety.py
python3 scripts/check_palomar_definition_identity.py --source-only
python3 scripts/verify_palomar_candidate.py
echo "PASS: local source/provenance/Comparator-layout/static-audit preflight."
echo "REMAINS: external consumer court, final exact-commit CI, independent publication approval"
echo "         and explicit owner approval of the exact GitHub push."
echo "NO PUSH, TAG, PR, COMMIT OR RELEASE WAS MADE BY THIS SCRIPT."
