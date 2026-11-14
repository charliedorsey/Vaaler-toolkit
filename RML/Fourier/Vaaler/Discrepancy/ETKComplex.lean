module

public import RML.Fourier.Vaaler.Discrepancy.MainFaceCompact
public import RML.Fourier.Vaaler.Discrepancy.FejerFaceCompact
public import RML.Fourier.Vaaler.Discrepancy.TorusBox

@[expose] public section

/-!
# Complex-frequency weighted torus ETK in arbitrary finite dimension

This theorem preserves independent cutoffs and wrapped half-open arcs.
For each nonempty coordinate face the main term is bounded by an explicit
finite signed complex frequency box. The Fejer-error term is bounded by
the norm of its exact finite complex frequency expression AFTER
subtracting the bare sample mass. No optimality claim is made.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- Conventional complex frequency form of the arbitrary-dimensional
weighted torus box discrepancy estimate. This norm-form bound retains
the exact Fejer zero-mode subtraction. -/
theorem weighted_torus_box_etk_complex
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : κ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb1 : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≠ b i) :
    |(∑ n ∈ N, w n * ∏ i,
       torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (Finset.univ : Finset κ).powerset.erase ∅,
      (mainFaceComplexBound A N w x J a b +
       ‖fejerFaceComplexSum A N w x J a b‖) := by
  classical
  have hETK := weighted_torus_box_etk N w hw x J hJ a b
    ha0 ha1 hb0 hb1 hab
  apply hETK.trans
  apply Finset.sum_le_sum
  intro A hA
  have hmain := mainFaceValue_abs_le_complexBound A N w x J a b
  rw [mainFaceValue_eq] at hmain
  have herr := fejerFaceValue_le_complex_norm A N w x J a b
  unfold fejerFaceValue at herr
  have hprod (n : ι) :
      (∏ i : A, (1 + intervalError (J i.1) (a i.1) (b i.1)
        (errorCoeff (J i.1)) (x n i.1))) =
      ∏ i ∈ A, (1 + intervalError (J i) (a i) (b i)
        (errorCoeff (J i)) (x n i)) :=
    Finset.prod_coe_sort A (fun i : κ =>
      (1 + intervalError (J i) (a i) (b i)
        (errorCoeff (J i)) (x n i)))
  simp_rw [hprod] at herr
  exact add_le_add hmain herr

#print axioms weighted_torus_box_etk_complex
end RML.Fourier.Vaaler.Positive
