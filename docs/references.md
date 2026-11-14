# References and sources

This is a mathematical-attribution guide, not a claim of a
line-for-line translation from each historical paper.

## Analytic origin

1. Jeffrey D. Vaaler, Some extremal functions in Fourier analysis,
   Bulletin of the American Mathematical Society (New Series)
   12 (1985), no. 2, 183–216.
   DOI: https://doi.org/10.1090/S0273-0979-1985-15349-2
   Historical Fourier extremal/majorant framework.
2. Paul Erdős and Pál Turán, On a problem in the theory
   of uniform distribution, Indagationes Mathematicae
   10 (1948), 370–378 and 406–413.
   Classical one-dimensional exponential-sum discrepancy approach.
3. J. F. Koksma, Some theorems on Diophantine inequalities,
   Mathematisch Centrum Amsterdam, Scriptum 5 (1950).
   Multidimensional distribution context.
4. L. Kuipers and H. Niederreiter, Uniform Distribution
   of Sequences, Wiley (1974). Exposition of the
   Erdős–Turán–Koksma inequality and its classical scope.

## Code and present formalization

5. Lean 4, official project:
   https://github.com/leanprover/lean4
6. Mathlib 4:
   https://github.com/leanprover-community/mathlib4
   Version pinned in this repository's lake-manifest.json.
7. Gershon Bialer, ternary-goldbach-lean:
   https://github.com/gersh/ternary-goldbach-lean
   The adapted FejerTriangle and SincSquare sources retain
   source-level copyright, licensing and modification notices.

The Vaaler–ETK Toolkit is a Lean formalization with explicitly
documented signed-weight, wrapping and labelled-frequency
extensions. It does not claim novelty of the historical classical
inequalities, sharp constants or complete coverage of all
forms found in the literature. Source provenance and ownership
are handled separately in docs/attribution.md and NOTICE.
