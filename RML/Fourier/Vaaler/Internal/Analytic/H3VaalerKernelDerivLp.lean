module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivLp

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable

theorem exists_bound_deriv_h3VaalerK :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |deriv h3VaalerK x| ≤ B := by
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
  refine ⟨max B 4, le_trans hB0 (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : |x| ≤ 1
  · exact (hB x hx).trans (le_max_left _ _)
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have hlarge := abs_deriv_h3VaalerK_le_inv_sq hx1
    have hx2 : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [sq_nonneg (|x| - 1)]
    have hinv : (x ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : 0 < x ^ 2)]
      exact hx2
    exact hlarge.trans <| by
      calc
        4 * (x ^ 2)⁻¹ ≤ 4 * 1 := by gcongr
        _ = 4 := by ring
        _ ≤ max B 4 := le_max_right _ _

theorem memLp_two_of_integrable_of_bounded {f : ℝ → ℂ}
    (hint : Integrable f)
    (hbdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) :
    MemLp f 2 (volume : Measure ℝ) := by
  obtain ⟨M, hb⟩ := hbdd
  rw [memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable]
  have hdom : Integrable (fun x => M * ‖f x‖) := hint.norm.const_mul M
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) volume := by fun_prop
  refine hdom.mono hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : ‖f x‖ ^ 2 ≤ M * ‖f x‖ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  exact hsq.trans (le_abs_self _)

theorem memLp_deriv_h3VaalerK_complex_two :
    MemLp (fun x : ℝ => ((deriv h3VaalerK x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by
  refine memLp_two_of_integrable_of_bounded
    integrable_deriv_h3VaalerK.ofReal ?_
  obtain ⟨B, _, hB⟩ := exists_bound_deriv_h3VaalerK
  refine ⟨B, fun x => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hB x

#print axioms exists_bound_deriv_h3VaalerK
#print axioms memLp_deriv_h3VaalerK_complex_two

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivLp
