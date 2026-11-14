module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerInterpHContinuous
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerInterpHContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous

theorem continuous_two_mul_re_h3VaalerJ :
    Continuous (fun x : ℝ => 2 * (h3VaalerJ x).re) := by
  exact continuous_const.mul (Complex.continuous_re.comp h3VaalerJ_continuous)

theorem integral_two_mul_re_h3VaalerJ_eq_sub (a b : ℝ) :
    (∫ x in a..b, 2 * (h3VaalerJ x).re) = h3InterpH b - h3InterpH a := by
  apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable
      h3InterpH (fun x : ℝ => 2 * (h3VaalerJ x).re)
      (Set.countable_range ((↑) : ℤ → ℝ))
  · exact h3InterpH_continuous.continuousOn
  · intro x hx
    exact hasDerivAt_h3InterpH_two_reJ_off_lattice hx.2
  · exact continuous_two_mul_re_h3VaalerJ.intervalIntegrable _ _

theorem h3InterpH_zero : h3InterpH 0 = 0 := by
  simp [h3InterpH]

theorem hasDerivAt_h3InterpH_two_reJ_global (x : ℝ) :
    HasDerivAt h3InterpH (2 * (h3VaalerJ x).re) x := by
  have hprim : HasDerivAt
      (fun u : ℝ => ∫ t in (0 : ℝ)..u, 2 * (h3VaalerJ t).re)
      (2 * (h3VaalerJ x).re) x :=
    intervalIntegral.integral_hasDerivAt_right
      (continuous_two_mul_re_h3VaalerJ.intervalIntegrable 0 x)
      continuous_two_mul_re_h3VaalerJ.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_two_mul_re_h3VaalerJ.continuousAt
  have hfun :
      (fun u : ℝ => ∫ t in (0 : ℝ)..u, 2 * (h3VaalerJ t).re) = h3InterpH := by
    funext u
    rw [integral_two_mul_re_h3VaalerJ_eq_sub, h3InterpH_zero, sub_zero]
  rwa [hfun] at hprim

#print axioms hasDerivAt_h3InterpH_two_reJ_global

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed
