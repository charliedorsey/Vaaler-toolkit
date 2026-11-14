module

public import RML.Fourier.Vaaler.Positive.Internal.VaalerRealInterior

@[expose] public section

namespace RML.Fourier.Vaaler.Positive

open RML.Fourier.Vaaler.Internal
open Finset

/-- Literal positive-frequency main coefficient in the H3 Vaaler normalization. -/
noncomputable def yevorin_vaalerMainCoeff (J j : ℕ) : ℂ :=
  (((h3VaalerJHat J (j : ℤ) / (Real.pi * (j : ℝ))) : ℝ) : ℂ) *
    Complex.I

/-- Positive-error Fejer coefficient; its Fourier polynomial has
constant term 1/(2*(J+1)) and these positive cosine modes. -/
noncomputable def yevorin_vaalerErrorCoeff (J j : ℕ) : ℂ :=
  (((1 - (j : ℝ) / ((J + 1 : ℕ) : ℝ)) /
      ((J + 1 : ℕ) : ℝ) : ℝ) : ℂ)

theorem yevorin_vaalerMainCoeff_norm_le (J j : ℕ) (hj : 1 ≤ j) :
    ‖yevorin_vaalerMainCoeff J j‖ ≤ (2 : ℝ) / j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hhat0 : 0 ≤ h3VaalerJHat J (j : ℤ) := h3VaalerJHat_nonneg J (j : ℤ)
  have hhat1 : h3VaalerJHat J (j : ℤ) ≤ 1 := h3VaalerJHat_le_one J (j : ℤ)
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hden : 0 < Real.pi * (j : ℝ) := by positivity
  have hsmall : h3VaalerJHat J (j : ℤ) / (Real.pi * (j : ℝ)) ≤ 2 / (j : ℝ) := by
    apply (div_le_div_iff₀ hden hjpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (show 0 ≤ (j : ℝ) from hjpos.le)]
  unfold yevorin_vaalerMainCoeff
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hhat0 hden.le)]
  exact hsmall

theorem yevorin_vaalerErrorCoeff_norm_le
    (J j : ℕ) (hj : j ∈ Finset.Icc 1 J) :
    ‖yevorin_vaalerErrorCoeff J j‖ ≤ (2 : ℝ) / (J + 1) := by
  have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
  have hd : (0 : ℝ) < (J + 1 : ℕ) := by positivity
  have hnr : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
  have hn0 : 0 ≤ 1 - (j : ℝ) / ((J + 1 : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one hd]
    push_cast
    linarith
  have hn1 : 1 - (j : ℝ) / ((J + 1 : ℕ) : ℝ) ≤ 1 := by
    have hp : 0 ≤ (j : ℝ) / ((J + 1 : ℕ) : ℝ) := by positivity
    linarith
  unfold yevorin_vaalerErrorCoeff
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hn0 hd.le)]
  have hi : (1 - (j : ℝ) / ((J + 1 : ℕ) : ℝ)) /
      ((J + 1 : ℕ) : ℝ) ≤ 1 / ((J + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hn1 hd.le
  have hcast : (((J + 1 : ℕ) : ℝ)) = (J : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hi ⊢
  exact hi.trans (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2)
    (by positivity : 0 ≤ (J : ℝ) + 1))

theorem yevorin_vaalerMainCoeff_mode_re
    (J j : ℕ) (t : ℝ) :
    (yevorin_vaalerMainCoeff J j * realVaalerMode j t).re =
      -(h3VaalerJHat J (j : ℤ) / (Real.pi * (j : ℝ))) *
          Real.sin (2 * Real.pi * (j : ℝ) * t) := by
  have hmode : realVaalerMode j t =
      Complex.exp (((2 * Real.pi * (j : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    unfold realVaalerMode
    congr 1
    push_cast
    ring
  rw [hmode, Complex.exp_ofReal_mul_I]
  unfold yevorin_vaalerMainCoeff
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, sub_zero, zero_sub]
  have hcomplex :
      (((Real.pi : ℂ) * (j : ℂ))⁻¹) =
        (((Real.pi * (j : ℝ))⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcomplex]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    zero_add, sub_zero]
  ring

theorem yevorin_vaalerMainCoeff_sum_eq_poly (J : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.Icc 1 J,
      (yevorin_vaalerMainCoeff J j * realVaalerMode j t).re) =
      (h3VaalerPolyReal J t).re := by
  rw [h3VaalerPolyReal_eq_sineSum]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [yevorin_vaalerMainCoeff_mode_re]
  ring

#print axioms yevorin_vaalerMainCoeff_norm_le
#print axioms yevorin_vaalerErrorCoeff_norm_le
#print axioms yevorin_vaalerMainCoeff_sum_eq_poly
end RML.Fourier.Vaaler.Positive
