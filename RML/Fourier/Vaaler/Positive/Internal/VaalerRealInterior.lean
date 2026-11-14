module

public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodizationCloseout
public import RML.Fourier.Vaaler.Positive.Core

@[expose] public section

/-! Source-faithful real Vaaler pointwise inequality on the open unit interval.
The jump value and finite positive Fourier error modes are separate steps.
No classical analytic estimate is assumed here. -/
namespace RML.Fourier.Vaaler.Positive

open RML.Fourier.Vaaler.Internal

theorem yevorin_vaaler_real_interior_norm
    (J : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ‖h3VaalerPolyReal J x - h3CenteredLinearC x‖ ≤
      h3RealFejerClosed J x / (2 * ((J + 1 : ℕ) : ℝ)) := by
  have hEq := h3ScaledVaalerPeriodizedC_eq_target_Ioo J
    (show x ∈ Set.Ioo (0 : ℝ) 1 from ⟨hx0, hx1⟩)
  have hx : ¬ ∃ m : ℤ, x = (m : ℝ) := by
    rintro ⟨m, hm⟩
    have hm0 : (0 : ℝ) < (m : ℝ) := hm ▸ hx0
    have hm1 : (m : ℝ) < 1 := hm ▸ hx1
    have hmge : (1 : ℤ) ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ (m : ℝ) by
      exact_mod_cast (Int.add_one_le_iff.mpr
        (show (0 : ℤ) < m by exact_mod_cast hm0)))
    have hmgeR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge
    linarith
  have hBound := h3ScaledVaalerError_periodized_abs_le_closed J hx
  have hNorm : ‖h3ScaledVaalerPeriodizedC J x‖ ≤
      h3RealFejerClosed J x := by
    rw [h3ScaledVaalerPeriodizedC_eq_ofReal]
    rw [← Complex.ofReal_tsum]
    simpa [Complex.norm_real, Real.norm_eq_abs] using hBound
  rw [hEq] at hNorm
  unfold h3PeriodizationTargetC at hNorm
  have hScale : (0 : ℝ) < 2 * ((J + 1 : ℕ) : ℝ) := by positivity
  have hScaleEq :
      ‖((2 * ((J + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ =
        2 * ((J + 1 : ℕ) : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hScale]
  rw [norm_mul] at hNorm
  have hScaleTerm :
      ‖(2 : ℂ) * (((J + 1 : ℕ) : ℝ) : ℂ)‖ =
        2 * ((J + 1 : ℕ) : ℝ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hScaleEq
  rw [hScaleTerm] at hNorm
  exact (le_div_iff₀ hScale).mpr (by nlinarith)

theorem yevorin_vaaler_real_interior_abs
    (J : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    |(h3VaalerPolyReal J x).re - (x - 1 / 2)| ≤
      h3RealFejerClosed J x / (2 * ((J + 1 : ℕ) : ℝ)) := by
  have hN := yevorin_vaaler_real_interior_norm J x hx0 hx1
  have hc : h3CenteredLinearC x = ((x - 1 / 2 : ℝ) : ℂ) := rfl
  rw [hc] at hN
  have hRe := Complex.abs_re_le_norm
    (h3VaalerPolyReal J x - ((x - 1 / 2 : ℝ) : ℂ))
  have heq : (h3VaalerPolyReal J x - ((x - 1 / 2 : ℝ) : ℂ)).re =
      (h3VaalerPolyReal J x).re - (x - 1 / 2) := by simp
  rw [heq] at hRe
  exact hRe.trans hN

#print axioms yevorin_vaaler_real_interior_norm
#print axioms yevorin_vaaler_real_interior_abs
end RML.Fourier.Vaaler.Positive
