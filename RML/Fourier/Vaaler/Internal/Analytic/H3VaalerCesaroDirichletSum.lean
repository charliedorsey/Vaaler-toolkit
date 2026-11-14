module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

noncomputable section

open Real
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroDirichletSum

theorem two_sin_mul_cos_odd (theta : ℝ) (N : ℕ) :
    2 * Real.sin theta * Real.cos ((2 * (N : ℝ) + 1) * theta) =
      Real.sin (2 * ((N : ℝ) + 1) * theta) - Real.sin (2 * (N : ℝ) * theta) := by
  have h1 : 2 * ((N : ℝ) + 1) * theta = (2 * (N : ℝ) + 1) * theta + theta := by ring
  have h2 : 2 * (N : ℝ) * theta = (2 * (N : ℝ) + 1) * theta - theta := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

theorem sum_cos_odd_telescope (theta : ℝ) (M : ℕ) :
    2 * Real.sin theta *
        (∑ N ∈ Finset.range M, Real.cos ((2 * (N : ℝ) + 1) * theta)) =
      Real.sin (2 * (M : ℝ) * theta) := by
  rw [Finset.mul_sum]
  induction M with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, two_sin_mul_cos_odd theta K]
      push_cast
      ring_nf

theorem sum_cos_odd_eq {theta : ℝ} (htheta : Real.sin theta ≠ 0) (M : ℕ) :
    (∑ N ∈ Finset.range M, Real.cos ((2 * (N : ℝ) + 1) * theta)) =
      Real.sin (2 * (M : ℝ) * theta) / (2 * Real.sin theta) := by
  have h2 : (2 : ℝ) * Real.sin theta ≠ 0 := by
    exact mul_ne_zero (by norm_num) htheta
  rw [eq_div_iff h2, mul_comm]
  exact sum_cos_odd_telescope theta M

#print axioms sum_cos_odd_eq

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroDirichletSum
