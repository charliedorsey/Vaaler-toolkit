module

public import RML.Fourier.Vaaler.Discrepancy.AbstractETK
public import RML.Fourier.Vaaler.Discrepancy.LocalInterval

@[expose] public section

/-! An actual weighted box-discrepancy inequality, over any finite coordinate type.
The approximants are real parts of explicit finite Vaaler Fourier sums.
This statement does NOT yet flatten the product into a single frequency-box sum.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Every half-open box, including all faces and integer-grid endpoints,
    admits a weighted Vaaler–Fejér ETK estimate with coordinate-dependent
    truncations and nonnegative sample weights. -/
theorem exists_weighted_box_etk
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i ≤ 1) :
    ∃ c e : κ → ℕ → ℂ,
      (∀ i j, j ∈ Finset.Icc 1 (J i) →
         ‖c i j‖ ≤ (2 : ℝ) / j ∧
         ‖e i j‖ ≤ (2 : ℝ) / (J i + 1)) ∧
      |(∑ n ∈ N, w n * ∏ i,
          (if a i ≤ Int.fract (x n i) ∧ Int.fract (x n i) < b i
           then (1 : ℝ) else 0)) -
        (∑ n ∈ N, w n) * ∏ i, (b i - a i)| ≤
      ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
        (|(∑ n ∈ N, w n *
            ∏ i ∈ A, intervalMain (J i) (a i) (b i) (c i) (x n i))| +
          ∑ n ∈ N, w n *
            (∏ i ∈ A,
              (1 + intervalError (J i) (a i) (b i) (e i) (x n i)) - 1)) := by
  classical
  have hlocal : ∀ i : κ, ∃ c e : ℕ → ℂ,
      (∀ j ∈ Finset.Icc 1 (J i),
        ‖c j‖ ≤ (2 : ℝ) / j ∧ ‖e j‖ ≤ (2 : ℝ) / (J i + 1)) ∧
      (∀ t : ℝ,
        (if a i ≤ Int.fract t ∧ Int.fract t < b i then (1 : ℝ) else 0) =
          (b i - a i) + intervalSigma (a i) (b i) t ∧
        |intervalSigma (a i) (b i) t| ≤ 1 ∧
        |intervalSigma (a i) (b i) t -
          intervalMain (J i) (a i) (b i) c t| ≤
          intervalError (J i) (a i) (b i) e t ∧
        0 ≤ intervalError (J i) (a i) (b i) e t) := by
    intro i
    exact exists_halfOpen_interval_certificate (J i) (hJ i)
      (a i) (b i) (ha i) (hab i) (hb i)
  choose c e hc using hlocal
  refine ⟨c, e, ?_, ?_⟩
  · intro i j hj
    exact (hc i).1 j hj
  have hlen0 : ∀ i, 0 ≤ b i - a i := by
    intro i
    linarith [hab i]
  have hlen1 : ∀ i, b i - a i ≤ 1 := by
    intro i
    linarith [ha i, hb i]
  have hsig : ∀ i t, |intervalSigma (a i) (b i) t| ≤ 1 := by
    intro i t
    exact ((hc i).2 t).2.1
  have herr : ∀ i t,
      |intervalSigma (a i) (b i) t -
          intervalMain (J i) (a i) (b i) (c i) t| ≤
        intervalError (J i) (a i) (b i) (e i) t := by
    intro i t
    exact ((hc i).2 t).2.2.1
  have hETK := ETKd.etk_abstract N w hw x
    (fun i => b i - a i) hlen0 hlen1
    (fun i t => intervalSigma (a i) (b i) t)
    (fun i t => intervalMain (J i) (a i) (b i) (c i) t)
    (fun i t => intervalError (J i) (a i) (b i) (e i) t)
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
    exact (((hc i).2 (x n i)).1).symm
  rw [hid] at hETK
  exact hETK

#print axioms exists_weighted_box_etk
end RML.Fourier.Vaaler.Positive
