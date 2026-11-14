# Vaaler–ETK Toolkit

**Constructive Fourier approximation and Erdős–Turán–Koksma discrepancy in Lean 4.**

**Raccoon Labs · Charlie Dorsey** — an RML (Raccoon Math Library) formalization.

**Version 0.1.0** · Lean 4.35.0 · pinned Mathlib · Apache-2.0

This toolkit provides importable finite-Fourier Vaaler and Fejér approximation certificates and discrepancy inequalities for **arbitrary finite-dimensional torus boxes**, with independent positive coordinate cutoffs, directed half-open wrapped or unwrapped arcs, and explicitly named coefficients. Its signed-weight extensions retain the sign in the oscillatory main term and charge approximation errors to absolute weights.

## What you can import

```lean
import RML.Fourier.Vaaler.Toolkit
open RML.Fourier.Vaaler.Positive

#check weighted_torus_box_etk
#check weighted_torus_box_etk_complex
#check weighted_torus_box_etk_signed
#check signed_torus_box_etk_frequency
#check signed_torus_box_etk_external_bounds
#check explicit_torus_arc_certificate
```

| Family | Exact role |
| --- | --- |
| `weighted_torus_box_etk` | Nonnegative real sample weights, named Vaaler approximation, mixed directed arcs |
| `weighted_torus_box_etk_complex` | Nonnegative weights, complex norm-form frequency-box bound with the Fejér subtraction inside the norm |
| `weighted_torus_box_etk_signed` | Arbitrary signed real weights and total-variation error charges |
| `signed_torus_box_etk_frequency` | Signed complex-frequency box with labelled frequencies, including explicit zero-mode accounting |
| `signed_torus_box_etk_external_bounds` | Consumer-supplied bounds for signed and absolute-weight exponential sums |

The exact theorem signatures, examples, and limits are in [current API guide](docs/API.md) and [scope notes](docs/scope.md).

## Mathematical scope and limitations

- Coordinates form any finite type, including dimension zero; each cutoff `J i` satisfies `1 ≤ J i`.
- Each coordinate has a directed half-open arc. For `a < b`, this means `[a,b)`; for `a > b`, the wrapped arc `[a,1) ∪ [0,b)`. The exact representatives `[0,1)` and `[1,0)` have distinct full and empty semantics.
- The theorem requiring `a ≠ b` does **not** silently choose the meaning of an equal-endpoint arc. Explicit empty/full constructors are available separately.
- Nonnegative-weight and signed-weight interfaces are distinct. Signed error terms use `∑ |w n|`, **not** `|∑ w n|`.
- Fourier tensor expressions retain labelled frequencies and multiplicities. No globally sharp coalesced coefficients, arbitrary polyhedral ETK, or rate-optimality claim is made.

The mathematics is a formalization and combination of classical analytical ideas, **not** a claim of historical priority.

## Verify and use locally

```sh
python3 scripts/verify_publication.py
python3 scripts/static_audit.py
python3 scripts/test_static_audit.py
python3 scripts/check_palomar_challenge_mirror.py
lake exe cache get
lake build RML.Fourier.Vaaler.Toolkit
for src in examples/*.lean; do lake env lean "$src"; done
lake env lean Solution.lean
python3 scripts/verify_challenge.py
python3 scripts/check_axioms.py
```

The deliberate proof hole in root `Challenge.lean` is **not part of the verified library**. Root `Challenge.lean` imports only Mathlib; root `Solution.lean` imports the proved signed theorem and has no proof holes. The original `challenge/` pair is retained as an internal pedagogical adapter. The source-text mirror checker and fourteen kernel-checked identities protect the source definitions. The official Comparator uses **no definition holes** (`"definition_names": []`) and its CI workflow requires both a genuine-proof PASS and a counterfeit-proof rejection for a constant-body mismatch.

See [verification](docs/verification.md), [publication gates](docs/release_gate.md), and [challenge notes](challenge/README.md).

## Provenance, rights and citation

Charlie Dorsey is the responsible human project director and the declared sole human contributor to the project-owned source. AI systems made substantial contributions to formal proof development, integration, source review, testing, and writing. The independent mathematical referee was an **AI reviewer**, not a human journal referee.

Two included analytic source files adapt Apache-2.0 work originally published by **Gershon Bialer**: `FejerTriangle.lean` and `SincSquare.lean`. Their source headers and [NOTICE](NOTICE) preserve attribution and modification disclosures. Mathlib and other Lake dependencies are **not vendored** into this repository and retain their own licenses. See [attribution](docs/attribution.md), [source provenance](docs/provenance.md), and [references](docs/references.md).

Suggested software citation: **Charlie Dorsey (Raccoon Labs), *Vaaler–ETK Toolkit*, v0.1.0, Lean 4 software**. Cite the exact released version using [CITATION.cff](CITATION.cff); cite historical mathematics separately. The license is [Apache-2.0](LICENSE).

## Verification and release

The source manifest, compiler/Mathlib pins, 115-file module-system
preservation audit, sixteen examples, thirteen named axioms, and fourteen
definition identities are checked by
[CI](.github/workflows/lean.yml). An independent Ubuntu workflow
[verifies the strict Comparator](.github/workflows/comparator-strict-linux.yml)
with active sandboxing and a counterfeit-proof negative control.
See [reproducibility](docs/verification.md) for exact commands and
[release gates](docs/release_gate.md) for the distinction between
technical acceptance, public GitHub publication, and Palomar registration.

To verify usability **outside this repository**, use a separate Lake project
depending on an immutable Git commit of this toolkit. The external consumer
court is independent of the sixteen in-tree examples.

This repository distributes the **public v0.1.0 source**. The exact Git
commit and its public CI receipts identify what has actually been verified.
GitHub publication is not Palomar submission, review or registration;
those actions require separate explicit authorization.
