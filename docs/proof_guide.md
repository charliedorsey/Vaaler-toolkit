# Vaaler-ETK proof dependency guide

The original 61 protected mathematical source modules retain their
pre-migration proof bodies, verified by the source-integrity auditor. The analytic
foundation builds pointwise sign/sawtooth interpolation and Fejer
sinc-square estimates, followed by explicit finite coefficients.

- Positive.Interval + ExplicitInterval: exact half-open pointwise
  sawtooth identity and finite-coefficient error majorant.
- Discrepancy.WeightedETK + AbstractETK: finite-face product
  discrepancy inequality for nonnegative weights in arbitrary
  finite dimension. The nonempty face family has cardinality
  2^d-1, including zero faces for d=0.
- Discrepancy.TorusBox: turns each coordinate's directed
  endpoint-correct certificate into a weighted torus box bound.
- Discrepancy.ArcChoice: explicit empty/full/directed arc choices.
- Discrepancy.SignedScalar + SignedTensor + LabelledTensor:
  exact positive/negative finite complex frequencies, arbitrary
  dependent frequency-label support and product expansions.
- Discrepancy.RealTensorBridge + MainFaceCompact:
  convert real main-polynomial face terms into finite complex
  exponential-sum frequency bounds.
- Discrepancy.FejerErrorLabels + FejerTensorComplex +
  FejerFaceCompact: maintain the exact zero-frequency coefficient
  1+2/(J+1), tensor-expand every error face and subtract the
  original sample mass INSIDE the complex norm.
- Discrepancy.ETKComplex: combine the previously proved
  nonnegative-weight ETK with both complex-frequency face bounds.
- Discrepancy.SignedETK: replace nonnegative sample weights in
  main terms by arbitrary real signed w, and move absolute values
  onto the error product bound; total variation is sum|w|.
- Discrepancy.SignedOneDimETK + SignedTorusBox:
  concrete one-dimensional signed Fourier certificate and named
  arbitrary finite-dimensional signed torus box inequality.
- Discrepancy.SignedFrequencyBox + SignedNegativeControl:
  explicit finite signed-frequency product, zero-mode separation,
  external bounds, and negative controls preventing the invalid
  substitution of |sum w| for sum|w|.

The namespaced labelled tensor interfaces distinguish the
dependent-label and uniform-label implementations:
weighted_tensor_expansion_labelled_uniform is the uniform-label
4B version; weighted_tensor_expansion_labelled is the dependent-label
4A version. Their mathematical statements are distinct and both
compile in the common namespace.

For readable entry points see examples/ETKComplex.lean,
examples/SignedTorusBox.lean, examples/SignedETK.lean,
examples/OneDimETK.lean and challenge/Solution.lean.

No assertion of identical algorithms, sharp coefficients, or
a complete original two-parameter ETK theorem is made outside
the exact proved statements.
