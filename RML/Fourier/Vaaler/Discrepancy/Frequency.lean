module

public import RML.Fourier.Vaaler.Discrepancy.ExplicitInterval

@[expose] public section

/-!
# Explicit finite-frequency representation for the VAALER interval certificate
The positive-frequency coefficients are literal complex numbers indexed by
1 <= j <= J. Real parts give the full real trigonometric polynomial.
No infinite Fourier series or hidden approximation support is used.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- The complex exponential obeys translation exactly in the Vaaler convention. -/
theorem realVaalerMode_sub (j : ℕ) (t u : ℝ) :
    realVaalerMode j (t - u) =
      realVaalerMode j (-u) * realVaalerMode j t := by
  unfold realVaalerMode
  have h : 2 * Real.pi * Complex.I * ((j : ℂ) * ((t - u : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * ((j : ℂ) * ((-u : ℝ) : ℂ)) +
      2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ)) := by
    push_cast
    ring
  rw [h, Complex.exp_add]

/-- The literal coefficient of positive Fourier frequency j for [a,b). -/
noncomputable def intervalFrequencyCoeff (J : ℕ) (a b : ℝ) (j : ℕ) : ℂ :=
  mainCoeff J j * (realVaalerMode j (-b) - realVaalerMode j (-a))

/-- The literal positive-frequency Fejér-error coefficient. -/
noncomputable def intervalErrorFrequencyCoeff (J : ℕ) (a b : ℝ) (j : ℕ) : ℂ :=
  errorCoeff J j * (realVaalerMode j (-b) + realVaalerMode j (-a))

theorem intervalMain_eq_frequency_sum
    (J : ℕ) (a b t : ℝ) :
    intervalMain J a b (mainCoeff J) t =
      ∑ j ∈ Finset.Icc 1 J,
        (intervalFrequencyCoeff J a b j * realVaalerMode j t).re := by
  unfold intervalMain approxMain
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [realVaalerMode_sub j t b, realVaalerMode_sub j t a]
  unfold intervalFrequencyCoeff
  rw [← Complex.sub_re]
  congr 1
  ring

theorem intervalError_eq_frequency_sum
    (J : ℕ) (a b t : ℝ) :
    intervalError J a b (errorCoeff J) t =
      (2 : ℝ) / (J + 1) +
        ∑ j ∈ Finset.Icc 1 J,
          (intervalErrorFrequencyCoeff J a b j * realVaalerMode j t).re := by
  unfold intervalError approxError
  calc
    ((1 : ℝ) / (J + 1) +
      ∑ j ∈ Finset.Icc 1 J, (errorCoeff J j * realVaalerMode j (t - b)).re) +
      ((1 : ℝ) / (J + 1) +
        ∑ j ∈ Finset.Icc 1 J, (errorCoeff J j * realVaalerMode j (t - a)).re) =
      (2 : ℝ) / (J + 1) +
        ((∑ j ∈ Finset.Icc 1 J,
            (errorCoeff J j * realVaalerMode j (t - b)).re) +
          (∑ j ∈ Finset.Icc 1 J,
            (errorCoeff J j * realVaalerMode j (t - a)).re)) := by ring
    _ = (2 : ℝ) / (J + 1) +
        ∑ j ∈ Finset.Icc 1 J,
          ((errorCoeff J j * realVaalerMode j (t - b)).re +
            (errorCoeff J j * realVaalerMode j (t - a)).re) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [realVaalerMode_sub j t b, realVaalerMode_sub j t a]
      unfold intervalErrorFrequencyCoeff
      rw [← Complex.add_re]
      congr 1
      ring

#print axioms realVaalerMode_sub
#print axioms intervalMain_eq_frequency_sum
#print axioms intervalError_eq_frequency_sum
end RML.Fourier.Vaaler.Positive
