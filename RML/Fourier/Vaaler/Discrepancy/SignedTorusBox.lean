module

public import RML.Fourier.Vaaler.Discrepancy.SignedETK
public import RML.Fourier.Vaaler.Discrepancy.TorusBox

@[expose] public section

/-!
# Tier 4B Phase II — named Vaaler signed torus-box ETK (VAALER-4B-R0002)

NEW extension module. Arbitrary finite coordinate type `κ` (including `Fin 0`), arbitrary
REAL sample weights (no sign hypothesis), coordinate-dependent cutoffs `J i ≥ 1`, and an
independently chosen directed half-open arc in every coordinate:
`a i < b i` gives `[a i, b i)`, `b i < a i` gives the wrapped arc `[a i, 1) ∪ [0, b i)`.
Equal endpoints are excluded exactly as in `weighted_torus_box_etk`; the explicit
empty/full constructors of `ArcChoice` are not reinterpreted.

The main summand of each nonempty face keeps the SIGNED weights; every Fejér error product
is weighted by `|w n|`. The existing `weighted_torus_box_etk` (TorusBox.lean) is unchanged
and is recovered under `w ≥ 0` by `weighted_torus_box_etk_of_signed`.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Directed-arc lengths lie in `[0,1]` (restated for the signed module; same proof as in
`weighted_torus_box_etk`). -/
theorem torusArcLength_mem_unit (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≠ b) :
    0 ≤ torusArcLength a b ∧ torusArcLength a b ≤ 1 := by
  unfold torusArcLength
  split_ifs with h
  · constructor <;> linarith
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)
    constructor <;> linarith

/-- **Signed constructive weighted ETK for mixed wrapped boxes in arbitrary finite
dimension.** No sign hypothesis on `w`. Named Vaaler coefficients `mainCoeff (J i)` and
`errorCoeff (J i)`; independent cutoffs and arc directions per coordinate. -/
theorem weighted_torus_box_etk_signed
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ)
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
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      (|(∑ n ∈ N, w n *
        ∏ i ∈ A,
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, |w n| *
          (∏ i ∈ A,
            (1 + intervalError (J i) (a i) (b i)
              (errorCoeff (J i)) (x n i)) - 1)) := by
  have hcert := fun i t => explicit_torus_arc_certificate (J i) (hJ i)
    (a i) (b i) (ha0 i) (ha1 i) (hb0 i) (hb1 i) (hab i) t
  have hETK := ETKd.etk_signed_abstract N w x
    (fun i => torusArcLength (a i) (b i))
    (fun i => (torusArcLength_mem_unit (a i) (b i) (ha0 i) (ha1 i) (hb0 i) (hb1 i) (hab i)).1)
    (fun i => (torusArcLength_mem_unit (a i) (b i) (ha0 i) (ha1 i) (hb0 i) (hb1 i) (hab i)).2)
    (fun i t => intervalSigma (a i) (b i) t)
    (fun i t => intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t)
    (fun i t => intervalError (J i) (a i) (b i) (errorCoeff (J i)) t)
    (fun i t => abs_intervalSigma_le_one (a i) (b i) t)
    (fun i t => (hcert i t).2.2.1)
  have hid : (∑ n ∈ N, w n *
      ∏ i, (torusArcLength (a i) (b i) + intervalSigma (a i) (b i) (x n i))) =
      ∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i) :=
    Finset.sum_congr rfl fun n _ => by
      congr 1
      exact Finset.prod_congr rfl fun i _ => ((hcert i (x n i)).1).symm
  rw [hid] at hETK
  exact hETK

/-- Every Fejér error value in the signed box theorem is nonnegative (derived from the named
certificate, not assumed). -/
theorem torus_box_error_nonneg
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≠ b) (t : ℝ) :
    0 ≤ intervalError J a b (errorCoeff J) t :=
  (explicit_torus_arc_certificate J hJ a b ha0 ha1 hb0 hb1 hab t).2.2.2

/-- **Recovery.** Under `w ≥ 0`, the signed box theorem yields exactly the statement of the
unchanged `weighted_torus_box_etk`. -/
theorem weighted_torus_box_etk_of_signed
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : κ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≠ b i) :
    |(∑ n ∈ N, w n * ∏ i,
        torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      (|(∑ n ∈ N, w n *
        ∏ i ∈ A,
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, w n *
          (∏ i ∈ A,
            (1 + intervalError (J i) (a i) (b i)
              (errorCoeff (J i)) (x n i)) - 1)) := by
  have h := weighted_torus_box_etk_signed N w x J hJ a b ha0 ha1 hb0 hb1 hab
  have hrw : ∀ A : Finset κ, ∑ n ∈ N, |w n| *
      (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1) =
      ∑ n ∈ N, w n *
      (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1) :=
    fun A => Finset.sum_congr rfl fun n hn => by rw [abs_of_nonneg (hw n hn)]
  simpa only [hrw] using h

#print axioms torusArcLength_mem_unit
#print axioms weighted_torus_box_etk_signed
#print axioms torus_box_error_nonneg
#print axioms weighted_torus_box_etk_of_signed

end RML.Fourier.Vaaler.Positive
