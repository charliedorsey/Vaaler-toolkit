module

public import RML.Fourier.Vaaler.Positive.Internal.VaalerCoefficients

@[expose] public section

namespace RML.Fourier.Vaaler.Positive

theorem yevorin_mode_add_int (j : ℕ) (t : ℝ) (m : ℤ) :
    realVaalerMode j (t + (m : ℝ)) = realVaalerMode j t := by
  unfold realVaalerMode
  have hphase :
      2 * Real.pi * Complex.I *
        ((j : ℂ) * (((t + (m : ℝ) : ℝ) : ℂ))) =
      2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ)) +
        ((((j : ℤ) * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [hphase, Complex.exp_add]
  have hperiod :
      Complex.exp ((((j : ℤ) * m : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨(j : ℤ) * m, rfl⟩
  rw [hperiod, mul_one]

theorem yevorin_mode_fract (j : ℕ) (t : ℝ) :
    realVaalerMode j (Int.fract t) = realVaalerMode j t := by
  calc
    realVaalerMode j (Int.fract t) =
        realVaalerMode j (Int.fract t + (⌊t⌋ : ℝ)) :=
          (yevorin_mode_add_int j (Int.fract t) ⌊t⌋).symm
    _ = realVaalerMode j t := by rw [Int.fract_add_floor]

theorem yevorin_saw_fract (t : ℝ) : saw (Int.fract t) = saw t := by
  simp [saw, Int.fract_fract]

theorem yevorin_saw_eq_neg_half_of_integer (t : ℝ)
    (ht : ∃ m : ℤ, t = (m : ℝ)) : saw t = -(1 / 2 : ℝ) := by
  obtain ⟨m, rfl⟩ := ht
  simp [saw, Int.fract_intCast]

theorem yevorin_fract_pos_of_noninteger (t : ℝ)
    (ht : ¬∃ m : ℤ, t = (m : ℝ)) : 0 < Int.fract t := by
  have hne : Int.fract t ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h
    exact ht ⟨m, hm.symm⟩
  exact lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hne)

#print axioms yevorin_mode_add_int
#print axioms yevorin_mode_fract
#print axioms yevorin_fract_pos_of_noninteger
end RML.Fourier.Vaaler.Positive
