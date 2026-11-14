# VAALER consumer examples

Each file is directly checked with the pinned Lean toolchain using

    lake env lean examples/NAME.lean

- Full.lean, Fejer.lean, Positive.lean and Pointwise.lean:
  foundational Vaaler and Fejér consumers.
- LocalInterval.lean: half-open interval identity and error certificate.
- WeightedETK.lean: Fin 1 and Fin 2 weighted discrepancy theorem use.
- TorusBox.lean: a mixed wrapped/ordinary box in Fin 2 with
  coordinate-specific cutoffs J=(3,7). This is the best first consumer
  to inspect for the general wrapped box theorem.

The new public entry point is RML.Fourier.Vaaler.Toolkit.
Use the theorem weighted_torus_box_etk for arbitrary finite dimension,
wrapped arcs, and independent cutoffs. Theorems currently use the real
tensor-mode Fourier presentation; flattened signed complex exponential
sum interfaces are now included in the signed frequency-box extensions;
see `SignedTorusBox.lean` and `ETKComplex.lean`.

- ArcChoice.lean: explicit empty/full versus directed half-open arcs.
- WeightedExponential.lean: explicit 1D main-polynomial bounds from
  externally supplied complex exponential-sum bounds B(j).
- OneDimETK.lean: one-dimensional discrepancy bound with explicit Fourier and Fejer error coefficients.
- SignedTensor.lean: arbitrary finite-dimensional signed complex frequency-box consumer and explicit Vaaler coefficient checks.

- LabelledTensor.lean: coefficients indexed by finite labelled frequency sets, including overlapping integer modes.

- FejerTensorComplex.lean: independent 2D cutoffs and zero-dimensional Fejér error exactness.

- ETKComplex.lean: 4A arbitrary-dimensional complex norm-form theorem, mixed wrapped/nonwrapped Fin 2 and Fin 0.

- SignedETK.lean: 4B signed abstract ETK, total variation, exact 1D error bounds and negative controls.

- SignedTorusBox.lean: 4B named signed-weight mixed torus boxes (Fin 2/4/0), flattened signed complex ETK and external bounds.
