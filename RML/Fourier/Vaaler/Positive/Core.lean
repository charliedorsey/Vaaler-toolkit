module

public import Mathlib

@[expose] public section

/-! The reusable Vaaler statement and exact centered-sawtooth convention. -/
namespace RML.Fourier.Vaaler.Positive

noncomputable def saw (t : ℝ) : ℝ := Int.fract t - 1 / 2

noncomputable def realVaalerMode (j : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ)))

def RealPositiveVaalerPointwise : Prop :=
  ∀ J : ℕ, 1 ≤ J →
    ∃ a b : ℕ → ℂ,
      (∀ j ∈ Finset.Icc 1 J,
        ‖a j‖ ≤ (2 : ℝ) / j ∧ ‖b j‖ ≤ (2 : ℝ) / (J + 1)) ∧
      (∀ t : ℝ,
        |saw t - ∑ j ∈ Finset.Icc 1 J,
          (a j * realVaalerMode j t).re| ≤
        (1 : ℝ) / (J + 1) +
        ∑ j ∈ Finset.Icc 1 J, (b j * realVaalerMode j t).re)

theorem saw_zero : saw 0 = -(1/2:ℝ) := by simp [saw]

end RML.Fourier.Vaaler.Positive
