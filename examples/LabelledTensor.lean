module

public import RML.Fourier.Vaaler.Discrepancy.LabelledTensor

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-- A reusable complex-frequency inequality with non-injective labels. -/
example {κ ι : Type*} [Fintype κ] [DecidableEq κ] {α : κ → Type*}
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : (i : κ) → Finset (α i))
    (freq : (i : κ) → α i → ℤ)
    (coeff : (i : κ) → α i → ℂ) :
    ‖∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ p ∈ C i,
         coeff i p * signedFourierMode (freq i p) (x n i)‖ ≤
    ∑ p ∈ Fintype.piFinset C,
      (∏ i, ‖coeff i (p i)‖) *
        ‖weightedTensorExponentialSum N w x (fun i => freq i (p i))‖ :=
  weighted_tensor_norm_le_exponential_sums_labelled N w x C freq coeff
