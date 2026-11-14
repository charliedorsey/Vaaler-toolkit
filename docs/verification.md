# Reproducing the release

The supported toolchain is `leanprover/lean4:v4.35.0` with Mathlib
pinned in `lake-manifest.json`. The publication archive consists of
tracked source files and the current `SHA256SUMS`, not build caches.

Run these commands from a clean exact checkout:

```sh
python3 scripts/verify_publication.py
python3 scripts/static_audit.py
python3 scripts/test_static_audit.py
python3 scripts/module_migration_integrity.py
python3 scripts/test_comparator_safety.py
python3 scripts/verify_palomar_candidate.py
python3 scripts/check_palomar_challenge_mirror.py
python3 scripts/check_palomar_definition_identity.py --source-only
lake exe cache get
lake build RML.Fourier.Vaaler.Toolkit Challenge Solution
for src in examples/*.lean; do lake env lean "$src"; done
python3 scripts/verify_challenge.py
python3 scripts/check_palomar_definition_identity.py
python3 scripts/check_axioms.py
```

The CI workflows under `.github/workflows/` run the full source check
and a **separate strict Linux Comparator**. The Comparator treats entries
in `definition_names` as *definition holes*: this project explicitly
sets `"definition_names": []`. A mirror text check alone is not enough.
The genuine Solution must pass, while
`tests/fixtures/CheatSolution.lean` must fail against the Challenge for
a **constant-body mismatch**. The Ubuntu workflow refuses to use
`--inadvisably-no-sandbox`.

For external use, create a new Lake project outside this checkout, with
a Git dependency on an **immutable** toolkit commit and a Lean source
that imports `RML.Fourier.Vaaler.Toolkit` and applies or checks the
named theorems. Run its own `lake update`, fetch the pinned cache and
compile the consumer. This catches missing exported modules, broken
imports and package-resolution errors that in-tree compilation might miss.

## Source provenance

`upstream/BASELINE_LEAN_SHA256.json` verifies the original 61
analytical modules with two explicitly allowed Bialer modification
notices. `upstream/R0024_PRE_MODULE_SOURCE_SHA256.json` and
`scripts/module_migration_integrity.py` establish preservation of
every Lean source body through the module-system conversion.

The full mathematical signature, not merely the theorem name, controls
the scope; see [API](API.md) and [theorems](theorems.md).

## Interpretation of receipts

A successful build proves only that its exact source compiles under the
reported toolchain. Separate evidence is necessary for the examples,
named axioms, source correspondence, Comparator genuine/cheat tests,
external package usability and publication rights. All CI receipts are
specific to their checked commits; they do **not** transfer to changed
source, even if the changes are editorial.
