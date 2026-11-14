module

public import RML.Fourier.Vaaler.Discrepancy.SignedTensor
public import RML.Fourier.Vaaler.Discrepancy.SignedScalar

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-- A black-box frequency-box consumer, at any finite dimension. -/
example {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : κ → Finset ℤ) (c : κ → ℤ → ℂ) :
    ‖∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ h ∈ C i, c i h * signedFourierMode h (x n i)‖ ≤
    ∑ h ∈ Fintype.piFinset C,
      (∏ i, ‖c i (h i)‖) * ‖weightedTensorExponentialSum N w x h‖ :=
  weighted_tensor_norm_le_exponential_sums N w x C c

/-- The two-sided Vaaler main polynomial has exact literal coefficients. -/
example (J : ℕ) (a b t : ℝ) :
    ((intervalMain J a b (mainCoeff J) t : ℝ) : ℂ) =
    ∑ p ∈ signedPairSupport J,
      signedMainCoeff J a b p *
        signedFourierMode (signedPairFrequency p) t :=
  signedMain_eq_two_sided J a b t

#check signedError_eq_two_sided
#check signedTensorMode_eq_dot
#check weighted_tensor_expansion
