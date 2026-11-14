module

public import RML.Fourier.Vaaler.Discrepancy.WeightedExponential

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-- Plug a bound for each S(j), j=1,2,3, into the explicit frequency formula. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (B : ℕ → ℝ)
    (hB : ∀ (j : ℕ), j ∈ Finset.Icc 1 3 →
      ‖weightedExponentialSum N w x (j : ℤ)‖ ≤ B j) :
    |∑ n ∈ N, w n *
      intervalMain 3 0 (1/2) (mainCoeff 3) (x n)| ≤
    ∑ j ∈ Finset.Icc 1 3,
      ‖intervalFrequencyCoeff 3 0 (1/2) j‖ * B j := by
  exact weighted_intervalMain_abs_le_external_sum_bounds
    N w x 3 0 (1/2) B hB

#check signedFourierMode_neg_nat
#check real_mode_eq_signed_pair
#check weighted_intervalMain_eq_exponential_sums
#check weighted_intervalMain_abs_le_exponential_sums
#check weighted_intervalMain_abs_le_external_sum_bounds
