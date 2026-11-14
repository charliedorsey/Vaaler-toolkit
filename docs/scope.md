# Vaaler–ETK mathematical scope

The original finite Fourier approximation toolkit has been extended
to concrete weighted Erdős-Turán-Koksma discrepancy inequalities.

1. Exact endpoint-aware half-open indicator identities, including
   integer jumps and wrapped torus arcs.
2. Named Vaaler main and Fejer error coefficients, finite
   explicit real and complex frequency expansions.
3. Arbitrary finite coordinate dimension (including dimension 0),
   unequal positive cutoffs and nonnegative unequal real sample weights.
4. Signed real sample weights, with signed oscillatory/main terms
   and absolute-weight approximation errors. This distinction is
   mathematically essential.
5. External-bound consumer interfaces with correct total variation
   and zero-frequency coefficients.
6. Explicit empty/full/directed arc constructors for ambiguous
   full-circle boundary representatives.

The Fourier frequency-box theorems retain labelled terms:
different labels may encode the same frequency, and coefficients
have not been optimally coalesced. There is no sharp constant or
optimal decay rate claim. The geometry is axis-parallel torus boxes,
not general polyhedra. The pointwise arithmetic inputs and
periodization wrappers maintain their exact source assumptions.

For a directed arc a,b in [0,1], a!=b:
a<b denotes [a,b); a>b denotes [a,1) union [0,b).
[0,1) is full and [1,0) is empty under exact representatives;
equal endpoints require choosing explicit constructors instead.

The full challenge/solution contract covers the signed torus-box
inequality, not every proved Fourier enhancement.
Formal theorem types control over prose; see docs/theorems.md.
