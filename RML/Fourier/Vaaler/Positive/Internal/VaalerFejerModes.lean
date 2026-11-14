module

public import RML.Fourier.Vaaler.Positive.Internal.FejerRealExpansion
public import RML.Fourier.Vaaler.Positive.Internal.VaalerPeriodic
public import RML.Fourier.Vaaler.Positive.Internal.VaalerIccRange

@[expose] public section

open Finset
namespace RML.Fourier.Vaaler.Positive

/-- Every reciprocal frequency has exactly the phase power in H3's Dirichlet sum. -/
theorem yevorin_phase_pow_eq_realVaalerMode (j : ℕ) (t : ℝ) :
    Complex.exp (Complex.I * (((2 * Real.pi * t : ℝ) : ℂ))) ^ j =
      realVaalerMode j t := by
  unfold realVaalerMode
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The prescribed positive Fejer coefficient is the triangular weight. -/
theorem yevorin_error_mode_triangle (J k : ℕ) (t : ℝ) :
    (yevorin_vaalerErrorCoeff J (k + 1) *
      realVaalerMode (k + 1) t).re =
      ((J : ℝ) - (k : ℝ)) / (((J + 1 : ℕ) : ℝ)^2) *
        (realVaalerMode (k + 1) t).re := by
  unfold yevorin_vaalerErrorCoeff
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hM : (J : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hM]
  ring

#print axioms yevorin_phase_pow_eq_realVaalerMode
#print axioms yevorin_error_mode_triangle
end RML.Fourier.Vaaler.Positive
