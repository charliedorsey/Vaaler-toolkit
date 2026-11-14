# Vaaler-ETK theorem inventory

The definitive theorem types and assumptions are the Lean sources.
Import RML.Fourier.Vaaler.Toolkit for the full public interface.

## Analytic foundations

- RML.Fourier.Vaaler.sign_approx_error_le: pointwise sign
  interpolant bounded by the nonnegative sinc-square Fejer kernel.
- RML.Fourier.Vaaler.kernel_fourier_fejer: normalized
  Fejer triangle Fourier transform, including support endpoints.
- RML.Fourier.Vaaler.error_fourier_transform_nonzero: its
  stated transform identity is specifically for NONZERO frequency.
- RML.Fourier.Vaaler.Positive.positive_pointwise:
  finite positive approximants with coefficient magnitude bounds.
- Positive.mainCoeff / errorCoeff: named explicit coefficients.
- Positive.explicit_halfOpen_interval_certificate:
  exact half-open jump normalization plus a pointwise majorant.

## Weighted discrepancy and arc semantics

- Positive.weighted_torus_box_etk: arbitrary finite coordinate
  type, nonnegative unequal weights, independent J_i>=1 and
  mixed directed wrapped/unwrapped half-open arcs. Errors are
  nonnegative tensor products; the discrepancy is bounded by
  a sum over all NONEMPTY coordinate faces.
- Positive.weighted_torus_box_etk_complex: same nonnegative
  setting, explicitly labelled signed complex main frequency
  sums and the NORM of the exact Fejer-error complex tensor
  with the bare sample mass subtracted before taking the norm.
- TorusArc.empty, TorusArc.full, TorusArc.directed:
  explicit zero/full/directed alternatives; a=b excluded
  from directed arc theorem, [0,1) full, [1,0) empty.

## Signed real weights / Tier 4B

- ETKd.signedWeightVariation: sum over N of absolute weights.
- ETKd.etk_signed_abstract: signed main terms, total-variation
  weighted errors and NO assumption that w_n is nonnegative.
- Positive.weighted_torus_box_etk_signed:
  constructive arbitrary-dimensional signed-weight torus box bound.
- Positive.signed_oneDim_etk_exponential and
  Positive.signed_oneDim_arc_etk_exponential:
  1D signed Fourier ETK with the Fejer error constant
  2*sum|w|/(J+1), not 2*|sum w|/(J+1).
- Positive.signed_torus_box_etk_frequency:
  explicit finite labelled frequencies. Signed S_w in main
  modes, absolute-weight S_|w| in errors. The error zero-mode
  coefficient for a face A is exactly
  (product over i in A of (1+2/(J_i+1)) - 1)*sum|w|.
- Positive.signed_torus_box_etk_external_bounds:
  consumer can provide independent bounds for S_w, S_|w|
  and an upper bound for total variation.

## Exact limitations

The signed-weight theorem does NOT bound approximation errors
by S_w alone. Labelled frequency vectors may repeat; this is
not a sharp coalesced scalar-frequency theorem. No general
polyhedral discrepancy result or unconstrained cutoffs is claimed.
Dimension zero means no nonempty faces and zero discrepancy.
The corresponding theorem declarations are compiled by the pinned
Lean build, and named axioms are checked independently. Publication
approval and registry acceptance remain separate gates.

See [API](API.md), [scope](scope.md), [examples](../examples/README.md)
and [challenge](../challenge/README.md) for consumer contracts.
