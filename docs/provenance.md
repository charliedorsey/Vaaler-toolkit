# Source provenance, rights and reproducibility

**Vaaler–ETK Toolkit · Raccoon Labs**

Charlie Dorsey is the responsible human maintainer and publication owner.
He has declared himself the sole human contributor to the project-owned
formalization and authorized its Apache-2.0 distribution. AI systems
contributed substantially to proofs, integration, review, testing and writing.
AI-based mathematical referee reports are not represented as human journal
peer review.

## Third-party source

Two analytic modules are adapted from Gershon Bialer's Apache-2.0
[ternary-goldbach-lean](https://github.com/gersh/ternary-goldbach-lean):

- `RML/Fourier/Vaaler/Internal/Analytic/FejerTriangle.lean`
- `RML/Fourier/Vaaler/Internal/Analytic/SincSquare.lean`

Their original headers, modification notices and publication attribution
remain in the source. See [LICENSE](../LICENSE) and [NOTICE](../NOTICE).
The changes include relocation into the RML namespace, the corresponding
import adjustments, and Lean 4.35 module-system wrappers. The mathematical
proof bodies have not been altered by the release preparations.

The Mathlib source and other Lake dependencies are **not included** in this
distribution; their exact revisions are recorded in
`lake-manifest.json` and they remain under their own licenses.

## Source-integrity evidence

Two necessary SHA-256 maps remain distributed with the source:

- `upstream/BASELINE_LEAN_SHA256.json`: the 61 frozen analytic source
  modules from the original toolkit, subject to exactly two disclosed
  Bialer modification notices.
- `upstream/R0024_PRE_MODULE_SOURCE_SHA256.json`: the original bytes of
  every Lean file before the required module-system migration.

Run `python3 scripts/static_audit.py` and
`python3 scripts/module_migration_integrity.py`. The latter reverses only
approved module headers/import visibility wrappers and verifies all 115
pre-migration Lean sources against their pinned hashes. Those checks detect
unauthorized changes to mathematical statements and proof bodies; the
full Lean build, axiom audit, consumer tests and independent Comparator
provide additional, separate mechanical evidence.

`SHA256SUMS` covers the **current** tracked source package, not any
earlier release snapshot. Historical planning notes and obsolete release
receipts are intentionally omitted from this public source distribution;
the private staging Git history and separately retained private audit
archives remain available to the maintainers; this public source repository
begins with a clean release snapshot. This is not an erasure of the upstream
authorship or source lineage.
