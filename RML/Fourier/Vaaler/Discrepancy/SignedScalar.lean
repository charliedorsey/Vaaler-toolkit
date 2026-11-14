module

public import RML.Fourier.Vaaler.Discrepancy.SignedTensor

@[expose] public section

/-!
# Exact two-sided finite Vaaler coefficients
For every 1 <= j <= J the two signed integer frequencies are +j and -j.
Using a pair (j, sign) keeps the support explicit without asking a
consumer to prove image injectivity.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- The explicit signed nonzero frequency index: j in {1,...,J},
with either positive or negative orientation. -/
noncomputable def signedPairSupport (J : ℕ) : Finset (ℕ × Bool) :=
  (Finset.Icc 1 J).product (Finset.univ : Finset Bool)

/-- The signed integer frequency denoted by a positive j and sign bit. -/
def signedPairFrequency (p : ℕ × Bool) : ℤ :=
  if p.2 then (p.1 : ℤ) else -(p.1 : ℤ)

/-- Positive- and negative-mode coefficients for the main polynomial. -/
noncomputable def signedMainCoeff (J : ℕ) (a b : ℝ)
    (p : ℕ × Bool) : ℂ :=
  if p.2 then intervalFrequencyCoeff J a b p.1 / 2
  else (starRingEnd ℂ) (intervalFrequencyCoeff J a b p.1) / 2

/-- Positive- and negative-mode coefficients for the Fejer error. -/
noncomputable def signedErrorCoeff (J : ℕ) (a b : ℝ)
    (p : ℕ × Bool) : ℂ :=
  if p.2 then intervalErrorFrequencyCoeff J a b p.1 / 2
  else (starRingEnd ℂ) (intervalErrorFrequencyCoeff J a b p.1) / 2

/-- Each real trigonometric term is exactly a signed pair of complex
characters, without approximations. -/
theorem signedMain_pair
    (J j : ℕ) (a b t : ℝ) :
    (((intervalFrequencyCoeff J a b j *
      realVaalerMode j t).re : ℝ) : ℂ) =
      ∑ q : Bool,
        signedMainCoeff J a b (j, q) *
          signedFourierMode (signedPairFrequency (j, q)) t := by
  rw [Fintype.sum_bool]
  simp only [signedMainCoeff, signedPairFrequency, ite_true]
  simpa [add_comm] using
    real_mode_eq_signed_pair j (intervalFrequencyCoeff J a b j) t

theorem signedError_pair
    (J j : ℕ) (a b t : ℝ) :
    (((intervalErrorFrequencyCoeff J a b j *
      realVaalerMode j t).re : ℝ) : ℂ) =
      ∑ q : Bool,
        signedErrorCoeff J a b (j, q) *
          signedFourierMode (signedPairFrequency (j, q)) t := by
  rw [Fintype.sum_bool]
  simp only [signedErrorCoeff, signedPairFrequency, ite_true]
  simpa [add_comm] using
    real_mode_eq_signed_pair j (intervalErrorFrequencyCoeff J a b j) t

/-- Exact finite integer-frequency expression of the real Vaaler main. -/
theorem signedMain_eq_two_sided
    (J : ℕ) (a b t : ℝ) :
    ((intervalMain J a b (mainCoeff J) t : ℝ) : ℂ) =
    ∑ p ∈ signedPairSupport J,
      signedMainCoeff J a b p *
        signedFourierMode (signedPairFrequency p) t := by
  rw [intervalMain_eq_frequency_sum, Complex.ofReal_sum]
  change _ = ∑ p ∈ (Finset.Icc 1 J) ×ˢ (Finset.univ : Finset Bool),
    signedMainCoeff J a b p * signedFourierMode (signedPairFrequency p) t
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  exact signedMain_pair J j a b t

/-- Exact finite integer-frequency expression of the Fejer error,
including its indispensable zero-frequency coefficient 2/(J+1). -/
theorem signedError_eq_two_sided
    (J : ℕ) (a b t : ℝ) :
    ((intervalError J a b (errorCoeff J) t : ℝ) : ℂ) =
    (2 : ℂ) / (J + 1) +
    ∑ p ∈ signedPairSupport J,
      signedErrorCoeff J a b p *
        signedFourierMode (signedPairFrequency p) t := by
  rw [intervalError_eq_frequency_sum]
  push_cast
  change _ = _ +
    ∑ p ∈ (Finset.Icc 1 J) ×ˢ (Finset.univ : Finset Bool),
      signedErrorCoeff J a b p *
        signedFourierMode (signedPairFrequency p) t
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  exact signedError_pair J j a b t

#print axioms signedMain_eq_two_sided
#print axioms signedError_eq_two_sided

end RML.Fourier.Vaaler.Positive
