module

public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodization
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

open scoped FourierTransform

namespace RML.Fourier.Vaaler.Internal

noncomputable def h3VaalerJHatReal (t : ℝ) : ℝ :=
  if t = 0 then 1
  else if |t| < 1 then
    Real.pi * |t| * (1 - |t|) * Real.cot (Real.pi * |t|) + |t|
  else 0

lemma h3_abs_int_div_succ (J : ℕ) (k : ℤ) :
    |(k : ℝ) / ((J + 1 : ℕ) : ℝ)| =
      (k.natAbs : ℝ) / ((J + 1 : ℕ) : ℝ) := by
  rw [abs_div]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((J + 1 : ℕ) : ℝ))]
  rw [Nat.cast_natAbs, Int.cast_abs]

lemma h3VaalerJHatReal_int_div (J : ℕ) (k : ℤ) :
    h3VaalerJHatReal ((k : ℝ) / ((J + 1 : ℕ) : ℝ)) =
      h3VaalerJHat J k := by
  by_cases hk0 : k = 0
  · subst k
    simp [h3VaalerJHatReal, h3VaalerJHat]
  · have hMpos : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by positivity
    have ht0 : (k : ℝ) / ((J + 1 : ℕ) : ℝ) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hk0) hMpos.ne'
    rw [h3VaalerJHatReal, if_neg ht0, h3_abs_int_div_succ]
    by_cases hband : k.natAbs ≤ J
    · have hlt : (k.natAbs : ℝ) / ((J + 1 : ℕ) : ℝ) < 1 := by
        rw [div_lt_one hMpos]
        exact_mod_cast Nat.lt_succ_of_le hband
      rw [if_pos hlt]
      unfold h3VaalerJHat
      rw [if_neg hk0, if_pos hband]
    · have hge : 1 ≤ (k.natAbs : ℝ) / ((J + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hMpos]
        have hnat : J + 1 ≤ k.natAbs :=
          Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hband)
        have hcast : (((J + 1 : ℕ) : ℝ)) ≤ (k.natAbs : ℝ) := by
          exact_mod_cast hnat
        simpa using hcast
      rw [if_neg (not_lt.mpr hge)]
      exact (h3VaalerJHat_eq_zero_of_band_lt
        (Nat.lt_of_not_ge hband)).symm

lemma h3VaalerSign_eq_sign (x : ℝ) :
    h3VaalerSign x = Real.sign x := by
  unfold h3VaalerSign
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx]
    simp [hx, not_lt.mpr hx.le]
  · subst x
    simp
  · rw [Real.sign_of_pos hx]
    simp [hx, not_lt.mpr hx.le]

def H3VaalerCor7TransformSpec : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    𝓕 (fun x : ℝ => ((h3VaalerSign x - h3VaalerH x : ℝ) : ℂ)) t
      =
    (((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹) *
      (1 - (h3VaalerJHatReal t : ℂ))

theorem h3Vaaler_sampled_source_of_cor7
    (hCor7 : H3VaalerCor7TransformSpec)
    (J : ℕ) (k : ℤ) (hk : k ≠ 0) :
    𝓕 (fun x : ℝ => ((h3VaalerSign x - h3VaalerH x : ℝ) : ℂ))
        ((k : ℝ) / ((J + 1 : ℕ) : ℝ))
      =
    (((J + 1 : ℕ) : ℝ) : ℂ) /
        ((Real.pi : ℂ) * Complex.I * (k : ℂ)) *
      (1 - (h3VaalerJHat J k : ℂ)) := by
  have hM : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have ht : (k : ℝ) / ((J + 1 : ℕ) : ℝ) ≠ 0 :=
    div_ne_zero hkR hM
  rw [hCor7 _ ht, h3VaalerJHatReal_int_div]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hMC : ((((J + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hM
  push_cast
  field_simp [hkC, hMC, Complex.I_ne_zero, Real.pi_ne_zero]

#print axioms h3VaalerSign_eq_sign
#print axioms h3Vaaler_sampled_source_of_cor7

end RML.Fourier.Vaaler.Internal
