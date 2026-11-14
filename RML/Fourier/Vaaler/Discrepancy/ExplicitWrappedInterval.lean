module

public import RML.Fourier.Vaaler.Discrepancy.WrappedInterval
public import RML.Fourier.Vaaler.Discrepancy.ExplicitInterval

@[expose] public section

/-! The wrapped-arc certificate with the named coefficients, valid at jumps. -/

namespace RML.Fourier.Vaaler.Positive

theorem explicit_wrapped_interval_certificate
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ 1)
    (t : ℝ) :
    (if a ≤ Int.fract t ∨ Int.fract t < b then (1 : ℝ) else 0) =
      (1 + b - a) + intervalSigma a b t ∧
    |intervalSigma a b t| ≤ 1 ∧
    |intervalSigma a b t -
      intervalMain J a b (mainCoeff J) t| ≤
      intervalError J a b (errorCoeff J) t ∧
    0 ≤ intervalError J a b (errorCoeff J) t := by
  have hpoint := explicit_halfOpen_interval_certificate
    J hJ b a hb hba ha t
  have hsigma : intervalSigma a b t = -intervalSigma b a t := by
    unfold intervalSigma
    ring
  have hmain : intervalMain J a b (mainCoeff J) t =
      -intervalMain J b a (mainCoeff J) t := by
    unfold intervalMain
    ring
  have herror : intervalError J a b (errorCoeff J) t =
      intervalError J b a (errorCoeff J) t := by
    unfold intervalError
    ring
  refine ⟨wrapped_indicator_eq_saw a b t hb hba ha, ?_, ?_, ?_⟩
  · exact abs_intervalSigma_le_one a b t
  · rw [hsigma, hmain, herror]
    simpa only [neg_sub_neg, abs_sub_comm] using hpoint.2.2.1
  · rw [herror]
    exact hpoint.2.2.2

#print axioms explicit_wrapped_interval_certificate
end RML.Fourier.Vaaler.Positive
