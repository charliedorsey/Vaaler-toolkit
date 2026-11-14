module

public import RML.Fourier.Vaaler.Discrepancy.SignedFrequency

@[expose] public section

/-!
# First consumer-facing complex exponential-sum inequality
This is the explicit one-dimensional main-polynomial conversion. The
Fejer-error and arbitrary-dimensional tensor conversion are separately
required to complete Tier 4A.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- The weighted Vaaler main polynomial is a finite sum of real parts of
the classical weighted complex exponential sums S(j). -/
theorem weighted_intervalMain_eq_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, w n *
      intervalMain J a b (mainCoeff J) (x n)) =
    ∑ j ∈ Finset.Icc 1 J,
      (intervalFrequencyCoeff J a b j *
        weightedExponentialSum N w x (j : ℤ)).re := by
  simp_rw [intervalMain_eq_frequency_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact weighted_mode_sum_real N w x j (intervalFrequencyCoeff J a b j)

/-- Explicit, computable frequency-weight bound in one dimension.
All modes occur at integer frequencies 1 through J. -/
theorem weighted_intervalMain_abs_le_exponential_sums
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (J : ℕ) (a b : ℝ) :
    |∑ n ∈ N, w n *
      intervalMain J a b (mainCoeff J) (x n)| ≤
    ∑ j ∈ Finset.Icc 1 J,
      ‖intervalFrequencyCoeff J a b j‖ *
        ‖weightedExponentialSum N w x (j : ℤ)‖ := by
  rw [weighted_intervalMain_eq_exponential_sums]
  calc
    |∑ j ∈ Finset.Icc 1 J,
      (intervalFrequencyCoeff J a b j *
        weightedExponentialSum N w x (j : ℤ)).re| ≤
      ∑ j ∈ Finset.Icc 1 J,
        |(intervalFrequencyCoeff J a b j *
          weightedExponentialSum N w x (j : ℤ)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 J,
        ‖intervalFrequencyCoeff J a b j‖ *
          ‖weightedExponentialSum N w x (j : ℤ)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        |(intervalFrequencyCoeff J a b j *
          weightedExponentialSum N w x (j : ℤ)).re|
            ≤ ‖intervalFrequencyCoeff J a b j *
                weightedExponentialSum N w x (j : ℤ)‖ :=
              Complex.abs_re_le_norm _
        _ = _ := norm_mul _ _

/-- Consumer version: plug in any proven upper bound B_j for the
    standard complex exponential sum S(j), rather than inspecting
    sample points directly. -/
theorem weighted_intervalMain_abs_le_external_sum_bounds
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (J : ℕ) (a b : ℝ)
    (B : ℕ → ℝ)
    (hB : ∀ j ∈ Finset.Icc 1 J,
      ‖weightedExponentialSum N w x (j : ℤ)‖ ≤ B j) :
    |∑ n ∈ N, w n *
      intervalMain J a b (mainCoeff J) (x n)| ≤
    ∑ j ∈ Finset.Icc 1 J,
      ‖intervalFrequencyCoeff J a b j‖ * B j := by
  apply (weighted_intervalMain_abs_le_exponential_sums N w x J a b).trans
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hB j hj) (norm_nonneg _)

#print axioms weighted_intervalMain_eq_exponential_sums
#print axioms weighted_intervalMain_abs_le_exponential_sums
#print axioms weighted_intervalMain_abs_le_external_sum_bounds
end RML.Fourier.Vaaler.Positive
