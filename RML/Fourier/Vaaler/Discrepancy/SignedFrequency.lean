module

public import RML.Fourier.Vaaler.Discrepancy.Frequency

@[expose] public section

/-! Classical integer-frequency exponential sums and exact signed pairs. -/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- The integer-indexed character with Vaaler's normalization. -/
noncomputable def signedFourierMode (h : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((h : ℂ) * (t : ℂ)))

/-- Finite weighted complex exponential sum, including negative modes. -/
noncomputable def weightedExponentialSum
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (h : ℤ) : ℂ :=
  ∑ n ∈ N, (w n : ℂ) * signedFourierMode h (x n)

theorem signedFourierMode_nat (j : ℕ) (t : ℝ) :
    signedFourierMode (j : ℤ) t = realVaalerMode j t := by
  simp [signedFourierMode, realVaalerMode]

theorem signedFourierMode_neg_nat (j : ℕ) (t : ℝ) :
    signedFourierMode (-(j : ℤ)) t =
      (starRingEnd ℂ) (realVaalerMode j t) := by
  change Complex.exp (2 * Real.pi * Complex.I *
    (((-(j : ℤ) : ℤ) : ℂ) * (t : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * (t : ℂ))))
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]

/-- Every real Vaaler positive mode splits into signed complex modes. -/
theorem real_mode_eq_signed_pair (j : ℕ) (c : ℂ) (t : ℝ) :
    ((c * realVaalerMode j t).re : ℂ) =
      (c / 2) * signedFourierMode (j : ℤ) t +
      ((starRingEnd ℂ) c / 2) * signedFourierMode (-(j : ℤ)) t := by
  rw [signedFourierMode_nat, signedFourierMode_neg_nat]
  rw [Complex.re_eq_add_conj]
  simp only [map_mul]
  ring

/-- Weighted real Fourier mode as a complex exponential sum. -/
theorem weighted_mode_sum_real
    {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (j : ℕ) (c : ℂ) :
    (∑ n ∈ N, w n * (c * realVaalerMode j (x n)).re) =
      (c * weightedExponentialSum N w x (j : ℤ)).re := by
  have hterm (n : ι) :
      w n * (c * realVaalerMode j (x n)).re =
        (((w n : ℂ) * c * realVaalerMode j (x n))).re := by
    simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, zero_mul, sub_zero]
    ring
  calc
    _ = ∑ n ∈ N, (((w n : ℂ) * c * realVaalerMode j (x n))).re := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n
    _ = (∑ n ∈ N, (w n : ℂ) * c * realVaalerMode j (x n)).re := by
      rw [Complex.re_sum]
    _ = (c * weightedExponentialSum N w x (j : ℤ)).re := by
      unfold weightedExponentialSum
      rw [mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [signedFourierMode_nat]
      ring

#print axioms signedFourierMode_neg_nat
#print axioms real_mode_eq_signed_pair
#print axioms weighted_mode_sum_real

end RML.Fourier.Vaaler.Positive
