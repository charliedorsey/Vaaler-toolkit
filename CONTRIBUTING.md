# Contributing to Vaaler–ETK Toolkit

**Raccoon Labs · Charlie Dorsey**

The supported toolchain is **Lean 4.35.0**, with the Mathlib commit pinned in
`lake-manifest.json`. Install the compiler named in `lean-toolchain` rather
than an older compatible-looking Lean release.

## Mathematical and source requirements

- Every Lean source file—including examples, Challenge, Solution and audit
  files—uses the Lean 4.35 `module` system. Public interfaces use explicit
  public imports and expose only intended declarations. Keep each file under
  Palomar's 10,000-line source cap.
- Do not add `sorry`, `admit`, custom axioms, `unsafe`, or opaque proof shortcuts
  to the verified RML library or either proved Solution.
- The **canonical** root `Challenge.lean` contains the one deliberate
  Palomar challenge `sorry`; `challenge/Challenge.lean` is a separate
  educational exercise with its own intentional hole. Neither challenge
  may be imported as a proof dependency by the proved library.
- Preserve exact source-theorem assumptions, endpoint conventions, coefficient
  definitions and the distinction between signed main terms and
  absolute-weight error terms. Changes to the mathematical library require a
  new, independent mathematical review and updated source-integrity baseline.
- The two adapted Gershon Bialer files retain their source-level copyright,
  original licensing, and explicit modification notices.
- Document API changes with compilable consumer examples; keep the canonical
  Challenge/Solution contract and strict `comparator.json` with
  `"definition_names": []`.

## Local verification

From a clean checkout:

```sh
python3 scripts/verify_publication.py
python3 scripts/static_audit.py
python3 scripts/test_static_audit.py
python3 scripts/module_migration_integrity.py
python3 scripts/verify_palomar_candidate.py
python3 scripts/test_comparator_safety.py
python3 scripts/check_palomar_challenge_mirror.py
lake exe cache get
lake build RML.Fourier.Vaaler.Toolkit Challenge Solution
for src in examples/*.lean; do lake env lean "$src"; done
python3 scripts/check_palomar_definition_identity.py
python3 scripts/check_axioms.py
python3 scripts/verify_challenge.py
```

A successful Lake build is not by itself an official Palomar Comparator PASS.
The official strict positive/negative Comparator court must run under a
functioning Linux sandbox without disabling Bubblewrap; its genuine Solution
must pass and its counterfeit must be rejected for a constant-body mismatch.

For a release candidate, refresh `SHA256SUMS` using
`python3 scripts/verify_publication.py --write`, commit the complete source,
recheck the manifest and rebuild against that exact commit.

## Release permissions

Repository review and private staging are not public publication. Public
GitHub release, Palomar preflight, submission, and permanent registration
require separate explicit authorization. See [release gates](docs/release_gate.md).
