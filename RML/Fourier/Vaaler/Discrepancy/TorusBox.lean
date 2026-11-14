module

public import RML.Fourier.Vaaler.Discrepancy.ExplicitWrappedInterval
public import RML.Fourier.Vaaler.Discrepancy.AbstractETK

@[expose] public section

/-!
# Weighted ETK on the torus: mixed wrapped/nonwrapped coordinate arcs
This works for any finite coordinate type (including Fin d), arbitrary
nonnegative sample weights and positive, coordinate-dependent cutoffs.
A coordinate with start > finish denotes [start,1) U [0,finish).
Equal endpoints are deliberately excluded: the empty/full convention
must be selected explicitly instead of silently guessing.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Length of a nondegenerate directed half-open arc on R/Z. -/
noncomputable def torusArcLength (a b : ℝ) : ℝ :=
  if a < b then b - a else 1 + b - a

/-- Literal membership of a directed half-open arc on the 1-torus. -/
noncomputable def torusArcIndicator (a b t : ℝ) : ℝ :=
  if a < b then
    (if a ≤ Int.fract t ∧ Int.fract t < b then 1 else 0)
  else
    (if a ≤ Int.fract t ∨ Int.fract t < b then 1 else 0)

/-- A directed arc has the exact centered sawtooth decomposition and
    constructive Vaaler majorant, including all boundary points. -/
theorem explicit_torus_arc_certificate
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : a ≠ b) (t : ℝ) :
    torusArcIndicator a b t =
      torusArcLength a b + intervalSigma a b t ∧
    |intervalSigma a b t| ≤ 1 ∧
    |intervalSigma a b t -
      intervalMain J a b (mainCoeff J) t| ≤
      intervalError J a b (errorCoeff J) t ∧
    0 ≤ intervalError J a b (errorCoeff J) t := by
  by_cases h : a < b
  · simpa only [torusArcIndicator, torusArcLength, if_pos h] using
      explicit_halfOpen_interval_certificate J hJ a b ha0 h hb1 t
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)
    simpa only [torusArcIndicator, torusArcLength, if_neg h] using
      explicit_wrapped_interval_certificate J hJ a b hb0 hgt ha1 t

/-- **Constructive weighted ETK for mixed wrapped boxes in arbitrary
    finite dimension.** Every coordinate has its own cutoff and its own
    left-closed/right-open directed arc. The RHS uses fully named finite
    Vaaler coefficient functions, not existentially chosen coefficients. -/
theorem weighted_torus_box_etk
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
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      (|(∑ n ∈ N, w n *
        ∏ i ∈ A,
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, w n *
          (∏ i ∈ A,
            (1 + intervalError (J i) (a i) (b i)
              (errorCoeff (J i)) (x n i)) - 1)) := by
  classical
  have hlen0 : ∀ i, 0 ≤ torusArcLength (a i) (b i) := by
    intro i
    by_cases h : a i < b i
    · simp only [torusArcLength, if_pos h]
      linarith
    · have hgt : b i < a i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hab i))
      simp only [torusArcLength, if_neg h]
      linarith [ha1 i, hb0 i]
  have hlen1 : ∀ i, torusArcLength (a i) (b i) ≤ 1 := by
    intro i
    by_cases h : a i < b i
    · simp only [torusArcLength, if_pos h]
      linarith [ha0 i, hb1 i]
    · have hgt : b i < a i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hab i))
      simp only [torusArcLength, if_neg h]
      linarith
  have hsig : ∀ i t, |intervalSigma (a i) (b i) t| ≤ 1 := by
    intro i t
    exact abs_intervalSigma_le_one (a i) (b i) t
  have herr : ∀ i t,
      |intervalSigma (a i) (b i) t -
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t| ≤
        intervalError (J i) (a i) (b i) (errorCoeff (J i)) t := by
    intro i t
    exact (explicit_torus_arc_certificate (J i) (hJ i)
      (a i) (b i) (ha0 i) (ha1 i) (hb0 i) (hb1 i) (hab i) t).2.2.1
  have hETK := ETKd.etk_abstract N w hw x
    (fun i => torusArcLength (a i) (b i)) hlen0 hlen1
    (fun i t => intervalSigma (a i) (b i) t)
    (fun i t => intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t)
    (fun i t => intervalError (J i) (a i) (b i) (errorCoeff (J i)) t)
    hsig herr
  have hid : (∑ n ∈ N, w n *
      ∏ i, (torusArcLength (a i) (b i) +
        intervalSigma (a i) (b i) (x n i))) =
      ∑ n ∈ N, w n * ∏ i,
        torusArcIndicator (a i) (b i) (x n i) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact (explicit_torus_arc_certificate (J i) (hJ i)
      (a i) (b i) (ha0 i) (ha1 i) (hb0 i) (hb1 i)
      (hab i) (x n i)).1.symm
  rw [hid] at hETK
  exact hETK

#print axioms explicit_torus_arc_certificate
#print axioms weighted_torus_box_etk
end RML.Fourier.Vaaler.Positive
