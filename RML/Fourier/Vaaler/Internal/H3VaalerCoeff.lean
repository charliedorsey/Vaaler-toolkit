module

public import RML.Fourier.Vaaler.Internal.FixedConductorCompletion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace RML.Fourier.Vaaler.Internal

/-- Vaaler's finite J-profile, specialized to the H3 degree parameter. -/
noncomputable def h3VaalerJHat (J : ℕ) (n : ℤ) : ℝ :=
  if n = 0 then 1 else if n.natAbs ≤ J then
    let t : ℝ := (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
    Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t
  else 0

@[simp] lemma h3VaalerJHat_zero (J : ℕ) : h3VaalerJHat J 0 = 1 := by
  simp [h3VaalerJHat]

lemma h3VaalerJHat_neg (J : ℕ) (n : ℤ) :
    h3VaalerJHat J (-n) = h3VaalerJHat J n := by
  unfold h3VaalerJHat
  rw [Int.natAbs_neg]
  by_cases hn : n = 0
  · subst n
    simp
  · have hneg : -n ≠ 0 := by omega
    simp [hn, hneg]

lemma h3VaalerJHat_eq_zero_of_band_lt {J : ℕ} {n : ℤ}
    (hn : J < n.natAbs) :
    h3VaalerJHat J n = 0 := by
  unfold h3VaalerJHat
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  simp [hn0, not_le.mpr hn]

/-- Positive-level kernel nonnegativity; finite coefficient half of Vaaler Thm. 18. -/
lemma h3VaalerJHat_kernel_nonneg {t : ℝ}
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    0 ≤ Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t := by
  by_cases ht_half : t ≤ (1 / 2 : ℝ)
  · have htheta_nonneg : 0 ≤ Real.pi * t := by positivity
    have htheta_le_half : Real.pi * t ≤ Real.pi / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht_half Real.pi_pos.le]
    have hsin_nonneg : 0 ≤ Real.sin (Real.pi * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi htheta_nonneg
        (by linarith [htheta_le_half, Real.pi_pos])
    have hcos_nonneg : 0 ≤ Real.cos (Real.pi * t) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) htheta_le_half
    have hcot_nonneg : 0 ≤ Real.cot (Real.pi * t) := by
      rw [Real.cot_eq_cos_div_sin]
      exact div_nonneg hcos_nonneg hsin_nonneg
    have h_one_sub_nonneg : 0 ≤ 1 - t := by linarith
    have hprod_nonneg :
        0 ≤ Real.pi * t * (1 - t) * Real.cot (Real.pi * t) := by
      positivity
    linarith
  · have ht_half_lt : (1 / 2 : ℝ) < t := lt_of_not_ge ht_half
    let u : ℝ := Real.pi * (1 - t)
    have hu_pos : 0 < u := by
      dsimp [u]
      positivity
    have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
    have hu_lt_half : u < Real.pi / 2 := by
      dsimp [u]
      nlinarith [Real.pi_pos, ht_half_lt]
    have hcos_pos : 0 < Real.cos u := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [hu_pos, hu_lt_half]
    have hsin_pos : 0 < Real.sin u := by
      apply Real.sin_pos_of_pos_of_lt_pi hu_pos
      linarith [hu_lt_half, Real.pi_pos]
    have htan := Real.le_tan hu_nonneg hu_lt_half
    have hu_cos_le_sin : u * Real.cos u ≤ Real.sin u := by
      rw [Real.tan_eq_sin_div_cos] at htan
      rwa [le_div_iff₀ hcos_pos] at htan
    have hcot_le_one : u * Real.cot u ≤ 1 := by
      rw [Real.cot_eq_cos_div_sin]
      rw [← mul_div_assoc]
      rw [div_le_one hsin_pos]
      exact hu_cos_le_sin
    have hfactor_nonneg : 0 ≤ 1 - u * Real.cot u := by linarith
    have hcot_rewrite : Real.cot (Real.pi * t) = -Real.cot u := by
      dsimp [u]
      rw [show Real.pi * t = Real.pi - Real.pi * (1 - t) by ring]
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      rw [Real.sin_pi_sub, Real.cos_pi_sub]
      ring
    rw [hcot_rewrite]
    have hmain :
        Real.pi * t * (1 - t) * (-Real.cot u) + t =
          t * (1 - u * Real.cot u) := by
      dsimp [u]
      ring
    rw [hmain]
    exact mul_nonneg (le_of_lt ht_pos) hfactor_nonneg

lemma h3VaalerJHat_nonneg (J : ℕ) (n : ℤ) :
    0 ≤ h3VaalerJHat J n := by
  unfold h3VaalerJHat
  by_cases hn0 : n = 0
  · simp [hn0]
  · rw [if_neg hn0]
    by_cases hband : n.natAbs ≤ J
    · rw [if_pos hband]
      let t : ℝ := (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
      have habs : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
      have ht0 : 0 < t := by
        dsimp [t]
        positivity
      have ht1 : t < 1 := by
        dsimp [t]
        rw [div_lt_one (by positivity : (0 : ℝ) < (J + 1 : ℕ))]
        exact_mod_cast Nat.lt_succ_of_le hband
      exact h3VaalerJHat_kernel_nonneg ht0 ht1
    · simp [hband]

/-- The sawtooth-side Fourier coefficient used in the endpoint-corrected polynomial. -/
noncomputable def h3VaalerSawCoeff (J : ℕ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    ((-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))⁻¹) *
      (h3VaalerJHat J n : ℂ)

@[simp] lemma h3VaalerSawCoeff_zero (J : ℕ) :
    h3VaalerSawCoeff J 0 = 0 := by
  simp [h3VaalerSawCoeff]

lemma h3VaalerSawCoeff_eq_zero_of_band_lt {J : ℕ} {n : ℤ}
    (hn : J < n.natAbs) :
    h3VaalerSawCoeff J n = 0 := by
  unfold h3VaalerSawCoeff
  rw [h3VaalerJHat_eq_zero_of_band_lt hn]
  simp

#print axioms h3VaalerJHat_nonneg
#print axioms h3VaalerSawCoeff_eq_zero_of_band_lt
end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

lemma h3VaalerJHat_kernel_le_one {t : ℝ}
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t ≤ 1 := by
  by_cases ht_half : t ≤ (1 / 2 : ℝ)
  · have htheta_pos : 0 < Real.pi * t := mul_pos Real.pi_pos ht_pos
    have htheta_le_half : Real.pi * t ≤ Real.pi / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht_half Real.pi_pos.le]
    rcases lt_or_eq_of_le htheta_le_half with hlt | heq
    · have htan := Real.le_tan htheta_pos.le hlt
      have hcos_pos : 0 < Real.cos (Real.pi * t) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith [Real.pi_pos, htheta_pos, hlt]
      have hsin_pos : 0 < Real.sin (Real.pi * t) := by
        apply Real.sin_pos_of_pos_of_lt_pi htheta_pos
        linarith [Real.pi_pos, hlt]
      rw [Real.tan_eq_sin_div_cos] at htan
      have hmul : (Real.pi * t) * Real.cos (Real.pi * t) ≤
          Real.sin (Real.pi * t) := by
        rwa [le_div_iff₀ hcos_pos] at htan
      have hcot : Real.pi * t * Real.cot (Real.pi * t) ≤ 1 := by
        rw [Real.cot_eq_cos_div_sin, ← mul_div_assoc, div_le_one hsin_pos]
        exact hmul
      have h1mt : 0 ≤ 1 - t := by linarith
      have hmul2 := mul_le_mul_of_nonneg_right hcot h1mt
      nlinarith
    · have ht_eq : t = 1 / 2 := by
        nlinarith [Real.pi_pos]
      subst t
      rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
      rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
  · have ht_half_lt : (1 / 2 : ℝ) < t := lt_of_not_ge ht_half
    have hangle_gt_half : Real.pi / 2 < Real.pi * t := by
      nlinarith [Real.pi_pos]
    have hangle_lt_pi : Real.pi * t < Real.pi := by
      nlinarith [Real.pi_pos, ht_lt_one]
    have hangle_lt_three_half : Real.pi * t < Real.pi + Real.pi / 2 := by
      linarith [hangle_lt_pi, Real.pi_pos]
    have hcos_neg : Real.cos (Real.pi * t) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hangle_gt_half hangle_lt_three_half
    have hsin_pos : 0 < Real.sin (Real.pi * t) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht_pos) hangle_lt_pi
    have hcot_nonpos : Real.cot (Real.pi * t) ≤ 0 := by
      rw [Real.cot_eq_cos_div_sin]
      exact div_nonpos_of_nonpos_of_nonneg hcos_neg.le hsin_pos.le
    have hbase : 0 ≤ Real.pi * t * (1 - t) := by positivity
    have hprod : Real.pi * t * (1 - t) * Real.cot (Real.pi * t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbase hcot_nonpos
    linarith

lemma h3VaalerJHat_le_one (J : ℕ) (n : ℤ) :
    h3VaalerJHat J n ≤ 1 := by
  unfold h3VaalerJHat
  by_cases hn0 : n = 0
  · simp [hn0]
  · rw [if_neg hn0]
    by_cases hband : n.natAbs ≤ J
    · rw [if_pos hband]
      let t : ℝ := (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
      have habs : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
      have ht0 : 0 < t := by
        dsimp [t]
        positivity
      have ht1 : t < 1 := by
        dsimp [t]
        rw [div_lt_one (by positivity : (0 : ℝ) < (J + 1 : ℕ))]
        exact_mod_cast Nat.lt_succ_of_le hband
      exact h3VaalerJHat_kernel_le_one ht0 ht1
    · simp [hband]

#print axioms h3VaalerJHat_le_one
end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Internal

lemma norm_h3VaalerSawCoeff_le
    (J : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ‖h3VaalerSawCoeff J n‖ ≤
      1 / (2 * Real.pi * (n.natAbs : ℝ)) := by
  unfold h3VaalerSawCoeff
  rw [if_neg hn]
  have hJ0 : 0 ≤ h3VaalerJHat J n := h3VaalerJHat_nonneg J n
  have hJ1 : h3VaalerJHat J n ≤ 1 := h3VaalerJHat_le_one J n
  have hnabs : 0 < (n.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hn
  rw [norm_mul, norm_inv]
  have hden :
      ‖(-2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ =
        2 * Real.pi * (n.natAbs : ℝ) := by
    rw [norm_mul, norm_mul, norm_mul]
    rw [Complex.norm_intCast, Complex.norm_I]
    norm_num
  rw [hden]
  have hreal : ‖(h3VaalerJHat J n : ℂ)‖ = h3VaalerJHat J n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJ0]
  rw [hreal]
  have hdenpos : 0 < 2 * Real.pi * (n.natAbs : ℝ) := by positivity
  calc
    (2 * Real.pi * (n.natAbs : ℝ))⁻¹ * h3VaalerJHat J n
        ≤ (2 * Real.pi * (n.natAbs : ℝ))⁻¹ * 1 := by
          gcongr
    _ = 1 / (2 * Real.pi * (n.natAbs : ℝ)) := by
          rw [one_div]
          ring

#print axioms norm_h3VaalerSawCoeff_le
end RML.Fourier.Vaaler.Internal
