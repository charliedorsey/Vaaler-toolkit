module

public import RML.Fourier.Vaaler.Pointwise

@[expose] public section

open RML.Fourier.Vaaler

-- A genuine use of the public (non-Internal) API.
example (x : ℝ) :
    |(if 0 < x then (1 : ℝ) else if x < 0 then -1 else 0) - H x| ≤ K x :=
  sign_approx_error_le x

example : K 0 = 1 := error_kernel_zero
example : H 0 = 0 := interpolant_zero
example (n : ℤ) : H (n : ℝ) = Real.sign (n : ℝ) := interpolant_int n

#print axioms RML.Fourier.Vaaler.sign_approx_error_le
