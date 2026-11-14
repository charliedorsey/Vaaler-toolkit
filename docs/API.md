# API guide — Vaaler–ETK Toolkit

**Supported environment:** Lean 4.35.0; Mathlib pinned by `lake-manifest.json`.
The authoritative declarations are the Lean modules under `RML/`.
This guide describes the current supported toolkit rather than historical
development stages.

## One import, several theorem families

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

| Family | What it proves |
| --- | --- |
| `weighted_torus_box_etk` | Nonnegative real sample weights; arbitrary finite coordinate type; wrapped and ordinary half-open directed arcs; independent positive cutoffs. |
| `weighted_torus_box_etk_complex` | Nonnegative-weight ETK controlled by labelled complex-frequency faces, subtracting the original mass **before** taking the Fejér error norm. |
| `weighted_torus_box_etk_signed` | Arbitrary **signed** real sample weights; oscillatory main terms retain sign; approximation errors charge total variation `∑ |w|`. |
| `signed_torus_box_etk_frequency` | Exact labelled signed and absolute-weight frequency-box expansion, retaining repeated labels and zero modes. |
| `signed_torus_box_etk_external_bounds` | Consumer-supplied upper bounds for signed and absolute-weight exponential sums, and total variation. |

For theorem statements and negative claims, see
[theorem inventory](theorems.md), [scope](scope.md), and
[proof dependencies](proof_guide.md).

## Analytic foundations

The pointwise sign approximation and its nonnegative error kernel are
available through `RML.Fourier.Vaaler.Pointwise`. The Fejér sinc-square
Fourier transform and periodization wrappers retain their exact
normalization and named source hypotheses; do not infer a value at zero
from the nonzero-frequency transform theorem.

The positive-weight finite-coefficient API provides named Vaaler main
coefficients, Fejér error coefficients, and pointwise half-open interval
certificates. In particular, `saw t = Int.fract t - 1/2`, including
the jump `saw 0 = -1/2`.

## Arc, cutoff, and sign contracts

A directed arc with `0 ≤ a,b ≤ 1` requires `a ≠ b`. For `a < b`
it denotes `[a,b)`; for `a > b` it wraps as
`[a,1) ∪ [0,b)`. The exact representatives `[0,1)` and
`[1,0)` represent full and empty arcs respectively. For equal
endpoints choose an explicit empty/full constructor instead.

Every coordinate cutoff is independently selected and at least one.
Coordinate type may be finite of size zero. Different labelled frequencies
can coincide: the interface does not assert optimally coalesced coefficients.

Do not replace error `∑ |w|` by `|∑ w|`. No theorem here claims
arbitrary polyhedral regions, best possible constants or unrestricted
equal-endpoint semantics.

## Getting started

Study the compiled examples under [examples](../examples/README.md).
For a first concrete box, use `examples/TorusBox.lean`; for the strongest
signed interface, use `examples/SignedTorusBox.lean`. The root
`Challenge.lean` and `Solution.lean` encode one canonical Palomar
signed-weight theorem from the broader library; see
[challenge documentation](../challenge/README.md).

For an independent package integration, create a separate Lake project
whose dependency is pinned to an immutable Git source commit. See the
[reproducibility guide](verification.md). The repository's own
sixteen examples are not a substitute for that external installation test.
