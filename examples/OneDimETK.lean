module

public import RML.Fourier.Vaaler.Discrepancy.OneDimETK

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-- Concrete 1D half-open weighted ETK, including the Fejér error.
A consumer can estimate S(j) with ordinary complex exponential sums. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → ℝ) :
    |(∑ n ∈ N, w n *
        (if (0 : ℝ) ≤ Int.fract (x n) ∧
           Int.fract (x n) < (1/2 : ℝ) then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * ((1/2 : ℝ) - 0)| ≤
      (2 : ℝ) / (3 + 1) * (∑ n ∈ N, w n) +
        ∑ j ∈ Finset.Icc 1 3,
          (‖intervalFrequencyCoeff 3 0 (1/2) j‖ +
            ‖intervalErrorFrequencyCoeff 3 0 (1/2) j‖) *
            ‖weightedExponentialSum N w x (j : ℤ)‖ := by
  exact weighted_oneDim_etk_exponential N w hw x 3 (by omega)
    0 (1/2) (by norm_num) (by norm_num) (by norm_num)

#check weighted_intervalError_eq_exponential_sums
#check weighted_intervalError_le_exponential_sums
#check weighted_oneDim_etk_exponential
