#!/usr/bin/env bash
# Explicit independent Linux reviewer utility, NEVER a live Palomar request.
# Execute ONLY in a sandbox-capable, NONROOT Linux environment.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "$(uname -s)" != "Linux" ]]; then
  echo "HOLD: official Comparator requires a separate sandbox-enabled Linux reviewer"; exit 2
fi
if [[ "$(id -u)" == "0" ]]; then
  echo "HOLD: do not run official Comparator as root"; exit 2
fi
if ! command -v bwrap >/dev/null 2>&1; then
  echo "HOLD: bwrap sandbox unavailable; do not bypass sandbox"; exit 2
fi
if [[ -n "$(git status --porcelain)" ]]; then
  echo "HOLD: source tree must be clean"; exit 2
fi
tmp="$(mktemp -d)"
evidence="${COMPARATOR_EVIDENCE_DIR:-$(pwd)/.local-replay/github-comparator-evidence}"
mkdir -p "$evidence"
printf 'commit=%s\nlean=%s\n' "$(git rev-parse HEAD)" "$(lean --version | head -1)" > "$evidence/context.txt"
finish() {
  rc=$?
  for f in positive.log negative.log cache.log; do
    if [[ -f "$tmp/$f" ]]; then cp "$tmp/$f" "$evidence/$f"; fi
  done
  printf '%s\n' "$rc" > "$evidence/runner_exit.txt"
  rm -rf "$tmp"
}
trap finish EXIT
# One scratch tree + one Mathlib cache. Earlier dual cold extractions
# exhausted the GitHub runner disk before a Comparator verdict existed.
mkdir -p "$tmp/work"
git archive HEAD | tar -xf - -C "$tmp/work"
echo "COMPARATOR_DISK_BEFORE_CACHE"
df -h "$tmp"
( cd "$tmp/work"; lake exe cache get ) > "$tmp/cache.log" 2>&1
echo "COMPARATOR_DISK_AFTER_CACHE"
df -h "$tmp"
# First prove the genuine, source-preserved Solution is accepted.
( cd "$tmp/work"; lake comparator --paranoid ) > "$tmp/positive.log" 2>&1
grep -F 'Your solution is okay!' "$tmp/positive.log" >/dev/null || {
  echo "HOLD: positive Comparator did not affirm actual Solution"; exit 1;
}
# Replace Solution in the SAME disposable tree only after the positive court.
# Evict any compiled Solution artifacts so the negative court cannot reuse a
# positive-court Solution. The full Mathlib dependency cache is retained.
cp tests/fixtures/CheatSolution.lean "$tmp/work/Solution.lean"
find "$tmp/work/.lake/build" -type f \( -name 'Solution.olean' -o -name 'Solution.ilean' -o -name 'Solution.c' -o -name 'Solution.o' \) -delete 2>/dev/null || true
echo "COMPARATOR_DISK_BEFORE_NEGATIVE"
df -h "$tmp"
set +e
( cd "$tmp/work"; lake comparator --paranoid ) > "$tmp/negative.log" 2>&1
negative_exit=$?
set -e
if [[ "$negative_exit" != "1" ]]; then
  echo "FAIL: falsifier not rejected by strict Comparator, exit=$negative_exit"; exit 1
fi
if ! grep -E -q 'Const does not match|does not match' "$tmp/negative.log"; then
  echo "HOLD: cheat rejected, but not for an established constant mismatch"; exit 1
fi
echo "PASS: genuine Solution accepted; cheat Solution rejected by constant-body mismatch"
echo "Evidence retained in $evidence"
