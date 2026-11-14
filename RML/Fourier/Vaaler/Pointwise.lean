module

public import RML.Fourier.Vaaler.Internal.H3VaalerPointwise

@[expose] public section

namespace RML.Fourier.Vaaler
open RML.Fourier.Vaaler.Internal

noncomputable abbrev H : ℝ → ℝ := h3VaalerH
noncomputable abbrev K : ℝ → ℝ := h3VaalerK

/-- Vaaler real sign approximation at every real number, including the integer grid. -/
theorem sign_approx_error_le (x : ℝ) :
    |(if 0 < x then (1 : ℝ) else if x < 0 then -1 else 0) - H x| ≤ K x :=
  h3Vaaler_sign_sub_abs_le_K x

theorem error_kernel_nonneg (x : ℝ) : 0 ≤ K x :=
  h3VaalerK_nonneg x

theorem error_kernel_zero : K 0 = 1 := h3VaalerK_zero
theorem interpolant_zero : H 0 = 0 := h3VaalerH_zero
theorem interpolant_int (n : ℤ) : H (n : ℝ) = Real.sign (n : ℝ) :=
  h3VaalerH_intCast n

#print axioms sign_approx_error_le
#print axioms error_kernel_nonneg
#print axioms error_kernel_zero
#print axioms interpolant_zero
#print axioms interpolant_int
end RML.Fourier.Vaaler
