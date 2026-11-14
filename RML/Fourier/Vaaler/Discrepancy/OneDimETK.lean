module

public import RML.Fourier.Vaaler.Discrepancy.WeightedExponential
public import RML.Fourier.Vaaler.Discrepancy.ExplicitInterval

@[expose] public section

/-!
# Full one-dimensional ETK in ordinary weighted complex exponential sums.
This is a nonsharp explicit finite estimate, with the Fejér error charged
to both its zero mode and its oscillatory modes, not simply omitted.
-/
namespace RML.Fourier.Vaaler.Positive
open Finset

/-- Exact Fourier conversion for the weighted Fejér approximation error. -/
theorem weighted_intervalError_eq_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, w n * intervalError J a b (errorCoeff J) (x n)) =
    (2 : ℝ) / (J + 1) * (∑ n ∈ N, w n) +
      ∑ j ∈ Finset.Icc 1 J,
        (intervalErrorFrequencyCoeff J a b j *
          weightedExponentialSum N w x (j : ℤ)).re := by
  simp_rw [intervalError_eq_frequency_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul]
    ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact weighted_mode_sum_real N w x j
      (intervalErrorFrequencyCoeff J a b j)

/-- The Fejér-error sum has explicit zero and oscillatory frequency
bounds (the zero-mode coefficient is exactly 2/(J+1)). -/
theorem weighted_intervalError_le_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, w n * intervalError J a b (errorCoeff J) (x n)) ≤
    (2 : ℝ) / (J + 1) * (∑ n ∈ N, w n) +
      ∑ j ∈ Finset.Icc 1 J,
        ‖intervalErrorFrequencyCoeff J a b j‖ *
          ‖weightedExponentialSum N w x (j : ℤ)‖ := by
  rw [weighted_intervalError_eq_exponential_sums]
  gcongr
  calc
    (intervalErrorFrequencyCoeff J a b j *
      weightedExponentialSum N w x (j : ℤ)).re
        ≤ ‖intervalErrorFrequencyCoeff J a b j *
          weightedExponentialSum N w x (j : ℤ)‖ := Complex.re_le_norm _
    _ = _ := norm_mul _ _

/-- The one-dimensional **classical** weighted ETK inequality, with
explicit Vaaler coefficients and the complete Fejér error. -/
theorem weighted_oneDim_etk_exponential
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → ℝ)
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    |(∑ n ∈ N, w n *
        (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
         then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * (b - a)| ≤
      (2 : ℝ) / (J + 1) * (∑ n ∈ N, w n) +
      ∑ j ∈ Finset.Icc 1 J,
        (‖intervalFrequencyCoeff J a b j‖ +
          ‖intervalErrorFrequencyCoeff J a b j‖) *
          ‖weightedExponentialSum N w x (j : ℤ)‖ := by
  have hpoint (n : ι) :=
    explicit_halfOpen_interval_certificate J hJ a b ha hab hb (x n)
  have hid :
      (∑ n ∈ N, w n *
        (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
          then (1 : ℝ) else 0)) -
        (∑ n ∈ N, w n) * (b - a) =
      ∑ n ∈ N, w n * intervalSigma a b (x n) := by
    simp_rw [show ∀ n : ι,
      (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
       then (1 : ℝ) else 0) =
      (b - a) + intervalSigma a b (x n) from fun n => (hpoint n).1]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hrem :
      |∑ n ∈ N, w n *
        (intervalSigma a b (x n) -
          intervalMain J a b (mainCoeff J) (x n))| ≤
        ∑ n ∈ N, w n *
          intervalError J a b (errorCoeff J) (x n) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro n hn
    rw [abs_mul, abs_of_nonneg (hw n hn)]
    exact mul_le_mul_of_nonneg_left ((hpoint n).2.2.1) (hw n hn)
  have hsplit :
      (∑ n ∈ N, w n * intervalSigma a b (x n)) =
        (∑ n ∈ N, w n *
          intervalMain J a b (mainCoeff J) (x n)) +
        (∑ n ∈ N, w n *
          (intervalSigma a b (x n) -
            intervalMain J a b (mainCoeff J) (x n))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hid, hsplit]
  calc
    |(∑ n ∈ N, w n *
        intervalMain J a b (mainCoeff J) (x n)) +
      (∑ n ∈ N, w n *
        (intervalSigma a b (x n) -
          intervalMain J a b (mainCoeff J) (x n)))| ≤
      |∑ n ∈ N, w n * intervalMain J a b (mainCoeff J) (x n)| +
        |∑ n ∈ N, w n *
          (intervalSigma a b (x n) -
            intervalMain J a b (mainCoeff J) (x n))| := abs_add_le _ _
    _ ≤ (∑ j ∈ Finset.Icc 1 J,
           ‖intervalFrequencyCoeff J a b j‖ *
             ‖weightedExponentialSum N w x (j : ℤ)‖) +
         (∑ n ∈ N, w n * intervalError J a b (errorCoeff J) (x n)) :=
      add_le_add (weighted_intervalMain_abs_le_exponential_sums N w x J a b) hrem
    _ ≤ (∑ j ∈ Finset.Icc 1 J,
           ‖intervalFrequencyCoeff J a b j‖ *
             ‖weightedExponentialSum N w x (j : ℤ)‖) +
        ((2 : ℝ) / (J + 1) * (∑ n ∈ N, w n) +
         ∑ j ∈ Finset.Icc 1 J,
           ‖intervalErrorFrequencyCoeff J a b j‖ *
             ‖weightedExponentialSum N w x (j : ℤ)‖) :=
      add_le_add_right
        (weighted_intervalError_le_exponential_sums N w x J a b) _
    _ = _ := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring

#print axioms weighted_intervalError_eq_exponential_sums
#print axioms weighted_intervalError_le_exponential_sums
#print axioms weighted_oneDim_etk_exponential
end RML.Fourier.Vaaler.Positive
