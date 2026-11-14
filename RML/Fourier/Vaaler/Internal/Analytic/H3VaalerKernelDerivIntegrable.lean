module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv

theorem abs_deriv_h3VaalerK_le_inv_sq {x : ℝ} (hx : 1 ≤ |x|) :
    |deriv h3VaalerK x| ≤ 4 * (x ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    linarith
  rw [deriv_h3VaalerK_offZero hx0]
  have hpi1 : (1 : ℝ) ≤ Real.pi := le_of_lt (by linarith [Real.pi_gt_three])
  have hsin : |Real.sin (Real.pi * x) / Real.pi| ≤ 1 := by
    rw [abs_div, abs_of_pos Real.pi_pos]
    have hs := Real.abs_sin_le_one (Real.pi * x)
    calc
      |Real.sin (Real.pi * x)| / Real.pi ≤ 1 / Real.pi :=
        div_le_div_of_nonneg_right hs Real.pi_pos.le
      _ ≤ 1 := by
        rw [div_le_one Real.pi_pos]
        exact hpi1
  have hcos : |Real.cos (Real.pi * x) * Real.pi / Real.pi| ≤ 1 := by
    rw [mul_div_cancel_right₀ _ Real.pi_ne_zero]
    exact Real.abs_cos_le_one _
  have hxabspos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have habsinv2 : |x⁻¹ ^ 2| = (x ^ 2)⁻¹ := by
    rw [abs_pow, abs_inv, inv_pow, sq_abs]
  have habsinv3 : |x⁻¹ ^ 3| = |x|⁻¹ ^ 3 := by
    rw [abs_pow, abs_inv]
  have hinv3_le_inv2 : |x|⁻¹ ^ 3 ≤ (x ^ 2)⁻¹ := by
    have hi0 : 0 ≤ |x|⁻¹ := by positivity
    have hi1 : |x|⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hxabspos]
      exact hx
    have hsq : |x|⁻¹ ^ 2 ≤ |x|⁻¹ := by nlinarith
    calc
      |x|⁻¹ ^ 3 = |x|⁻¹ ^ 2 * |x|⁻¹ := by ring
      _ ≤ |x|⁻¹ * |x|⁻¹ := mul_le_mul_of_nonneg_right hsq hi0
      _ = |x|⁻¹ ^ 2 := by ring
      _ = (x ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
  have hfirst :
      |2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2|
        ≤ 2 * (x ^ 2)⁻¹ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |Real.sin (Real.pi * x) / Real.pi| *
            |Real.cos (Real.pi * x) * Real.pi / Real.pi| * |x⁻¹ ^ 2|
          ≤ 2 * 1 * 1 * |x⁻¹ ^ 2| := by gcongr
      _ = 2 * (x ^ 2)⁻¹ := by rw [habsinv2]; ring
  have hsin_sq : |Real.sin (Real.pi * x) / Real.pi| ^ 2 ≤ 1 := by
    have h0 : 0 ≤ |Real.sin (Real.pi * x) / Real.pi| := abs_nonneg _
    have := pow_le_pow_left₀ h0 hsin 2
    simpa using this
  have hsecond :
      |2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3|
        ≤ 2 * (x ^ 2)⁻¹ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
    calc
      2 * |Real.sin (Real.pi * x) / Real.pi| ^ 2 * |x⁻¹ ^ 3|
          ≤ 2 * 1 * |x⁻¹ ^ 3| := by gcongr
      _ = 2 * (|x|⁻¹ ^ 3) := by rw [habsinv3]; ring
      _ ≤ 2 * (x ^ 2)⁻¹ := by gcongr
  calc
    |2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3|
      ≤ |2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2|
        + |2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3| := abs_sub _ _
    _ ≤ 2 * (x ^ 2)⁻¹ + 2 * (x ^ 2)⁻¹ := add_le_add hfirst hsecond
    _ = 4 * (x ^ 2)⁻¹ := by ring

theorem integrable_deriv_h3VaalerK :
    Integrable (deriv h3VaalerK) (volume : Measure ℝ) := by
  have hcont : Continuous (deriv h3VaalerK) :=
    contDiff_h3VaalerK.continuous_deriv (by simp)
  obtain ⟨B, hB0, hB⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |x| ≤ 1 → |deriv h3VaalerK x| ≤ B := by
    have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
    obtain ⟨C, hC⟩ := (hcompact.image hcont.abs).bddAbove
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro x hx
    have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc]
      exact abs_le.mp hx
    have hmem : |deriv h3VaalerK x| ∈
        (fun y => |deriv h3VaalerK y|) '' Set.Icc (-1 : ℝ) 1 :=
      ⟨x, hxmem, rfl⟩
    exact le_trans (hC hmem) (le_max_left _ _)
  refine Integrable.mono'
    (integrable_inv_one_add_sq.const_mul (max 8 (2 * B)))
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  have hdenpos : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 1
  · have hBnd := hB x hx
    have hx2 : x ^ 2 ≤ 1 := by
      have hsq : |x| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg x) hx 2
      rwa [sq_abs, one_pow] at hsq
    have hinv : (1 / 2 : ℝ) ≤ (1 + x ^ 2)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      apply inv_anti₀ hdenpos
      linarith
    calc
      |deriv h3VaalerK x| ≤ B := hBnd
      _ ≤ (2 * B) * (1 + x ^ 2)⁻¹ := by
        have := mul_le_mul_of_nonneg_left hinv hB0
        nlinarith
      _ ≤ (max 8 (2 * B)) * (1 + x ^ 2)⁻¹ := by
        gcongr
        exact le_max_right _ _
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have hlarge := abs_deriv_h3VaalerK_le_inv_sq hx1
    have hx2 : 1 ≤ x ^ 2 := by rw [← sq_abs]; nlinarith [sq_nonneg (|x| - 1)]
    have hinv : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have hx2pos : 0 < x ^ 2 := by positivity
      rw [show (x ^ 2)⁻¹ = 1 / x ^ 2 by rw [one_div],
        show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hx2pos hdenpos]
      nlinarith [hx2]
    calc
      |deriv h3VaalerK x| ≤ 4 * (x ^ 2)⁻¹ := hlarge
      _ ≤ 8 * (1 + x ^ 2)⁻¹ := by nlinarith
      _ ≤ (max 8 (2 * B)) * (1 + x ^ 2)⁻¹ := by
        gcongr
        exact le_max_left _ _

#print axioms integrable_deriv_h3VaalerK

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable
