module

public import RML.Fourier.Vaaler.Discrepancy.AbstractETK
public import RML.Fourier.Vaaler.Discrepancy.ExplicitInterval

@[expose] public section

/-!
# Constructive weighted ETK for boxes in arbitrary finite dimensions.
No existential coefficient choice is needed: the polynomial uses public
mainCoeff and errorCoeff at each cutoff J i.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Named-coefficient weighted box discrepancy with arbitrary finite
coordinates and independent positive cutoffs. The RHS is a finite sum
over nonempty coordinate faces and is completely determined by the input. -/
theorem weighted_box_etk_explicit
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i ≤ 1) :
    |(∑ n ∈ N, w n * ∏ i,
        (if a i ≤ Int.fract (x n i) ∧ Int.fract (x n i) < b i
         then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * ∏ i, (b i - a i)| ≤
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      (|(∑ n ∈ N, w n *
        ∏ i ∈ A,
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, w n *
          (∏ i ∈ A,
            (1 + intervalError (J i) (a i) (b i)
              (errorCoeff (J i)) (x n i)) - 1)) := by
  classical
  have hlen0 : ∀ i, 0 ≤ b i - a i := by
    intro i
    linarith [hab i]
  have hlen1 : ∀ i, b i - a i ≤ 1 := by
    intro i
    linarith [ha i, hb i]
  have hsig : ∀ i t, |intervalSigma (a i) (b i) t| ≤ 1 := by
    intro i t
    exact (explicit_halfOpen_interval_certificate
      (J i) (hJ i) (a i) (b i) (ha i) (hab i) (hb i) t).2.1
  have herr : ∀ i t,
      |intervalSigma (a i) (b i) t -
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t| ≤
        intervalError (J i) (a i) (b i) (errorCoeff (J i)) t := by
    intro i t
    exact (explicit_halfOpen_interval_certificate
      (J i) (hJ i) (a i) (b i) (ha i) (hab i) (hb i) t).2.2.1
  have hETK := ETKd.etk_abstract N w hw x
    (fun i => b i - a i) hlen0 hlen1
    (fun i t => intervalSigma (a i) (b i) t)
    (fun i t => intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t)
    (fun i t => intervalError (J i) (a i) (b i) (errorCoeff (J i)) t)
    hsig herr
  have hid : (∑ n ∈ N, w n *
      ∏ i, ((b i - a i) + intervalSigma (a i) (b i) (x n i))) =
      ∑ n ∈ N, w n *
        ∏ i, (if a i ≤ Int.fract (x n i) ∧ Int.fract (x n i) < b i
               then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact (explicit_halfOpen_interval_certificate
      (J i) (hJ i) (a i) (b i) (ha i) (hab i) (hb i) (x n i)).1.symm
  rw [hid] at hETK
  exact hETK

#print axioms weighted_box_etk_explicit
end RML.Fourier.Vaaler.Positive
