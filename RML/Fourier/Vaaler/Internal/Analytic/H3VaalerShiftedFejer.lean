module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv

theorem shifted_h3VaalerK_eq (z : ℝ) (m : ℤ)
    (hzm : z - (m : ℝ) ≠ 0) :
    (Real.sin (Real.pi * z) / Real.pi) ^ 2 *
        (z - (m : ℝ))⁻¹ ^ 2 =
      h3VaalerK (z - m) := by
  unfold h3VaalerK
  rw [if_neg hzm]
  have hsin :
      Real.sin (Real.pi * (z - (m : ℝ))) =
        (-1) ^ m * Real.sin (Real.pi * z) := by
    have hrw :
        Real.pi * (z - (m : ℝ)) =
          Real.pi * z - (m : ℝ) * Real.pi := by ring
    rw [hrw, Real.sin_sub_int_mul_pi]
  rw [hsin]
  have h1 : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← zpow_natCast ((-1 : ℝ) ^ m) 2, ← zpow_mul]
    rw [show (m * (2 : ℕ) : ℤ) = 2 * m by push_cast; ring, zpow_mul]
    norm_num
  rw [div_pow, div_pow, mul_pow, h1]
  field_simp [Real.pi_ne_zero, hzm]

theorem hasDerivAt_invSq_shift (c x : ℝ)
    (hx : x - c ≠ 0) :
    HasDerivAt (fun y : ℝ => (y - c)⁻¹ ^ 2)
      (-2 * (x - c)⁻¹ ^ 3) x := by
  have hinner : HasDerivAt (fun y : ℝ => y - c) 1 x := by
    simpa using (hasDerivAt_id x).sub_const c
  have hinv := hinner.inv hx
  refine (hinv.pow 2).congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp [hx]
  have hcancel : (x - c) * (x - c)⁻¹ = 1 := mul_inv_cancel₀ hx
  calc
    _ = -2 * ((x - c) * (x - c)⁻¹) := by ring
    _ = -2 := by rw [hcancel]; ring

theorem hasDerivAt_h3VaalerK_shift_offInt {n : ℤ} {x : ℝ}
    (hxn : x - (n : ℝ) ≠ 0) :
    HasDerivAt (fun y : ℝ => h3VaalerK (y - (n : ℝ)))
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          (x - (n : ℝ))⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * (x - (n : ℝ))⁻¹ ^ 3)) x := by
  have hsinpi : HasDerivAt
      (fun y : ℝ => Real.sin (Real.pi * y))
      (Real.cos (Real.pi * x) * Real.pi) x := by
    have hinner : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    exact (Real.hasDerivAt_sin (Real.pi * x)).comp x hinner
  have hdiv : HasDerivAt
      (fun y : ℝ => Real.sin (Real.pi * y) / Real.pi)
      (Real.cos (Real.pi * x) * Real.pi / Real.pi) x :=
    hsinpi.div_const Real.pi
  have hsq : HasDerivAt
      (fun y : ℝ => (Real.sin (Real.pi * y) / Real.pi) ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
        (Real.cos (Real.pi * x) * Real.pi / Real.pi)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  have hinvsq := hasDerivAt_invSq_shift (n : ℝ) x hxn
  have hprod : HasDerivAt
      (fun y : ℝ =>
        (Real.sin (Real.pi * y) / Real.pi) ^ 2 *
          (y - (n : ℝ))⁻¹ ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          (x - (n : ℝ))⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * (x - (n : ℝ))⁻¹ ^ 3)) x := by
    refine (hsq.mul hinvsq).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  have hne : ∀ᶠ y : ℝ in nhds x, y - (n : ℝ) ≠ 0 := by
    exact ((continuous_id.sub continuous_const).continuousAt).eventually_ne hxn
  have heq :
      (fun y : ℝ =>
        (Real.sin (Real.pi * y) / Real.pi) ^ 2 *
          (y - (n : ℝ))⁻¹ ^ 2)
        =ᶠ[nhds x]
      (fun y : ℝ => h3VaalerK (y - (n : ℝ))) := by
    filter_upwards [hne] with y hy
    exact shifted_h3VaalerK_eq y n hy
  exact hprod.congr_of_eventuallyEq heq.symm

theorem sub_posShift_ne_zero {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) (m : ℕ) :
    x - ((m : ℝ) + 1) ≠ 0 := by
  intro h
  apply hs
  have hxm : x = ((m : ℝ) + 1) := by linarith
  rw [hxm,
    show Real.pi * ((m : ℝ) + 1) =
      ((↑m + 1 : ℤ) : ℝ) * Real.pi by push_cast; ring,
    Real.sin_int_mul_pi]

theorem add_posShift_ne_zero {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) (m : ℕ) :
    x + ((m : ℝ) + 1) ≠ 0 := by
  intro h
  apply hs
  have hxm : x = -((m : ℝ) + 1) := by linarith
  rw [hxm,
    show Real.pi * -((m : ℝ) + 1) =
      (-(↑m + 1) : ℤ) * Real.pi by push_cast; ring,
    Real.sin_int_mul_pi]

theorem hasDerivAt_h3VaalerK_posShift (m : ℕ) {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    HasDerivAt (fun y : ℝ => h3VaalerK (y + ((m : ℝ) + 1)))
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          (x + ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3)) x := by
  have hxn : x - ((-(↑m + 1) : ℤ) : ℝ) ≠ 0 := by
    have hne := add_posShift_ne_zero hs m
    push_cast
    intro h
    apply hne
    linarith
  have h :=
    hasDerivAt_h3VaalerK_shift_offInt
      (n := (-(↑m + 1) : ℤ)) (x := x) hxn
  have hcast :
      (((-(↑m + 1) : ℤ)) : ℝ) = -((m : ℝ) + 1) := by
    push_cast
    ring
  rw [hcast] at h
  simp only [sub_neg_eq_add] at h
  exact h

#print axioms hasDerivAt_h3VaalerK_shift_offInt
#print axioms hasDerivAt_h3VaalerK_posShift

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer
