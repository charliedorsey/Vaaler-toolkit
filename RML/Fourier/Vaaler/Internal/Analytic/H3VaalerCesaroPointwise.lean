module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
public import Mathlib.Analysis.PSeries

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators ContDiff

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous

theorem summable_negSq (x : ℝ) :
    Summable (fun m : ℕ => (x - ((m : ℝ) + 1))⁻¹ ^ 2) := by
  rw [← summable_norm_iff]
  have h := (Real.summable_one_div_nat_add_rpow (1 - x) 2).2 (by norm_num)
  refine h.congr (fun m => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_inv]
  have heq : |x - ((m : ℝ) + 1)| = |(m : ℝ) + (1 - x)| := by
    rw [show x - ((m : ℝ) + 1) = -((m : ℝ) + (1 - x)) by ring, abs_neg]
  rw [heq, one_div, ← Real.rpow_natCast]
  norm_num

theorem summable_posSq (x : ℝ) :
    Summable (fun m : ℕ => (x + ((m : ℝ) + 1))⁻¹ ^ 2) := by
  rw [← summable_norm_iff]
  have h := (Real.summable_one_div_nat_add_rpow (x + 1) 2).2 (by norm_num)
  refine h.congr (fun m => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_inv]
  have heq : |x + ((m : ℝ) + 1)| = |(m : ℝ) + (x + 1)| := by
    congr 1 <;> ring
  rw [heq, one_div, ← Real.rpow_natCast]
  norm_num

theorem summable_negCube (x : ℝ) :
    Summable (fun m : ℕ => (x - ((m : ℝ) + 1))⁻¹ ^ 3) := by
  rw [← summable_norm_iff]
  have h := (Real.summable_one_div_nat_add_rpow (1 - x) 3).2 (by norm_num)
  refine h.congr (fun m => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_inv]
  have heq : |x - ((m : ℝ) + 1)| = |(m : ℝ) + (1 - x)| := by
    rw [show x - ((m : ℝ) + 1) = -((m : ℝ) + (1 - x)) by ring, abs_neg]
  rw [heq, one_div, ← Real.rpow_natCast]
  norm_num

theorem summable_posCube (x : ℝ) :
    Summable (fun m : ℕ => (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  rw [← summable_norm_iff]
  have h := (Real.summable_one_div_nat_add_rpow (x + 1) 3).2 (by norm_num)
  refine h.congr (fun m => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_inv]
  have heq : |x + ((m : ℝ) + 1)| = |(m : ℝ) + (x + 1)| := by
    congr 1 <;> ring
  rw [heq, one_div, ← Real.rpow_natCast]
  norm_num

def dShift (x : ℝ) (m : ℕ) : ℝ :=
  deriv h3VaalerK (x - ((m : ℝ) + 1)) -
    deriv h3VaalerK (x + ((m : ℝ) + 1))

theorem deriv_h3VaalerK_negShift (m : ℕ) {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    deriv h3VaalerK (x - ((m : ℝ) + 1)) =
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          (x - ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * (x - ((m : ℝ) + 1))⁻¹ ^ 3) := by
  have hk : HasDerivAt h3VaalerK
      (deriv h3VaalerK (x - ((m : ℝ) + 1)))
      (x - ((m : ℝ) + 1)) :=
    (contDiff_h3VaalerK.differentiable (by simp)).differentiableAt.hasDerivAt
  have hshift :
      deriv (fun y : ℝ => h3VaalerK (y - ((m : ℝ) + 1))) x =
        deriv h3VaalerK (x - ((m : ℝ) + 1)) :=
    (hk.comp_sub_const x ((m : ℝ) + 1)).deriv
  have hxn : x - (((↑m + 1 : ℤ)) : ℝ) ≠ 0 := by
    have h := sub_posShift_ne_zero hs m
    push_cast
    exact h
  have h := hasDerivAt_h3VaalerK_shift_offInt
    (n := (↑m + 1 : ℤ)) (x := x) hxn
  have hcast : (((↑m + 1 : ℤ)) : ℝ) = (m : ℝ) + 1 := by
    push_cast; ring
  rw [hcast] at h
  rw [← hshift, h.deriv]

theorem deriv_h3VaalerK_posShift_pt (m : ℕ) {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    deriv h3VaalerK (x + ((m : ℝ) + 1)) =
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          (x + ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  have hk : HasDerivAt h3VaalerK
      (deriv h3VaalerK (x + ((m : ℝ) + 1)))
      (x + ((m : ℝ) + 1)) :=
    (contDiff_h3VaalerK.differentiable (by simp)).differentiableAt.hasDerivAt
  have hshift :
      deriv (fun y : ℝ => h3VaalerK (y + ((m : ℝ) + 1))) x =
        deriv h3VaalerK (x + ((m : ℝ) + 1)) :=
    (hk.comp_add_const x ((m : ℝ) + 1)).deriv
  rw [← hshift, (hasDerivAt_h3VaalerK_posShift m hs).deriv]

theorem dShift_closed (m : ℕ) {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    dShift x m =
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          ((x - ((m : ℝ) + 1))⁻¹ ^ 2 -
            (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          ((x - ((m : ℝ) + 1))⁻¹ ^ 3 -
            (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  rw [dShift, deriv_h3VaalerK_negShift m hs,
    deriv_h3VaalerK_posShift_pt m hs]
  ring

theorem summable_dShift {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    Summable (dShift x) := by
  have hsumcl : Summable (fun m : ℕ =>
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          ((x - ((m : ℝ) + 1))⁻¹ ^ 2 -
            (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          ((x - ((m : ℝ) + 1))⁻¹ ^ 3 -
            (x + ((m : ℝ) + 1))⁻¹ ^ 3)) := by
    apply Summable.sub
    · exact (((summable_negSq x).sub (summable_posSq x)).mul_left _)
    · exact (((summable_negCube x).sub (summable_posCube x)).mul_left _)
  exact hsumcl.congr (fun m => (dShift_closed m hs).symm)

theorem tsum_dShift {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    ∑' m : ℕ, dShift x m =
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) *
          ((∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 2) -
            ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          ((∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 3) -
            ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  rw [tsum_congr (fun m => dShift_closed m hs)]
  rw [Summable.tsum_sub
      (((summable_negSq x).sub (summable_posSq x)).mul_left _)
      (((summable_negCube x).sub (summable_posCube x)).mul_left _)]
  rw [(((summable_negSq x).sub (summable_posSq x))).tsum_mul_left,
      (((summable_negCube x).sub (summable_posCube x))).tsum_mul_left]
  rw [(summable_negSq x).tsum_sub (summable_posSq x),
      (summable_negCube x).tsum_sub (summable_posCube x)]

theorem deriv_HNcore_eq (N : ℕ) (x : ℝ) :
    deriv (HNcore N) x = ∑ m ∈ Finset.range N, dShift x m := by
  have heach : ∀ m ∈ Finset.range N,
      HasDerivAt (fun z : ℝ =>
        h3VaalerK (z - ((m : ℝ) + 1)) -
          h3VaalerK (z + ((m : ℝ) + 1)))
        (dShift x m) x := by
    intro m _
    have hsub0 : HasDerivAt h3VaalerK
        (deriv h3VaalerK (x - ((m : ℝ) + 1)))
        (x - ((m : ℝ) + 1)) :=
      (contDiff_h3VaalerK.differentiable (by simp)).differentiableAt.hasDerivAt
    have hadd0 : HasDerivAt h3VaalerK
        (deriv h3VaalerK (x + ((m : ℝ) + 1)))
        (x + ((m : ℝ) + 1)) :=
      (contDiff_h3VaalerK.differentiable (by simp)).differentiableAt.hasDerivAt
    exact (hsub0.comp_sub_const x ((m : ℝ) + 1)).sub
      (hadd0.comp_add_const x ((m : ℝ) + 1))
  have hs := HasDerivAt.sum (u := Finset.range N)
    (A := fun m z => h3VaalerK (z - ((m : ℝ) + 1)) -
      h3VaalerK (z + ((m : ℝ) + 1)))
    (A' := fun m => dShift x m) heach
  have hfun :
      (∑ i ∈ Finset.range N, fun z : ℝ =>
        h3VaalerK (z - ((i : ℝ) + 1)) -
          h3VaalerK (z + ((i : ℝ) + 1))) = HNcore N := by
    funext z
    rw [HNcore, Finset.sum_apply]
  rw [hfun] at hs
  exact hs.deriv

theorem tendsto_deriv_HNcore {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    Tendsto (fun N : ℕ => deriv (HNcore N) x) atTop
      (nhds (∑' m : ℕ, dShift x m)) := by
  have htend := (summable_dShift hs).hasSum.tendsto_sum_nat
  refine htend.congr (fun N => ?_)
  rw [deriv_HNcore_eq N x]

theorem deriv_tailFn (x : ℝ) :
    deriv tailFn x =
      2 * h3VaalerK x + 2 * x * deriv h3VaalerK x := by
  have hk : HasDerivAt h3VaalerK (deriv h3VaalerK x) x :=
    (contDiff_h3VaalerK.differentiable (by simp)).differentiableAt.hasDerivAt
  have hid : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  exact ((hid.mul hk).congr_deriv (by ring)).deriv

theorem half_S_add_half_dtail_eq_h3G {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    (1 / 2 : ℝ) * (∑' m : ℕ, dShift x m) +
        (1 / 2 : ℝ) * deriv tailFn x =
      h3G x := by
  have hx0 : x ≠ 0 := by
    intro h
    apply hs
    simp [h]
  have hdtail :
      deriv tailFn x =
        4 * (Real.sin (Real.pi * x) / Real.pi) *
            (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹
          - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 2 := by
    rw [deriv_tailFn, deriv_h3VaalerK_offZero hx0]
    unfold h3VaalerK
    rw [if_neg hx0]
    field_simp [Real.pi_ne_zero]
    ring
  rw [tsum_dShift hs, hdtail, h3G_eq_of_ne_zero hx0,
    h3InterpBracket, h3TailSum]
  have hM2 :
      (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) =
        ∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 2 :=
    tsum_congr (fun m => by push_cast; ring_nf)
  have hP2 :
      (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) =
        ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 2 :=
    tsum_congr (fun m => by push_cast; ring_nf)
  have hM3neg :
      (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
        (x - (k + 1 : ℕ))⁻¹) =
        -2 * ∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 3 := by
    rw [show (-2 : ℝ) * ∑' m : ℕ,
        (x - ((m : ℝ) + 1))⁻¹ ^ 3 =
      ∑' m : ℕ, -2 * (x - ((m : ℝ) + 1))⁻¹ ^ 3
      from (tsum_mul_left).symm]
    exact tsum_congr (fun m => by push_cast; ring_nf)
  have hP3neg :
      (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
        (x + (k + 1 : ℕ))⁻¹) =
        -2 * ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 3 := by
    rw [show (-2 : ℝ) * ∑' m : ℕ,
        (x + ((m : ℝ) + 1))⁻¹ ^ 3 =
      ∑' m : ℕ, -2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3
      from (tsum_mul_left).symm]
    exact tsum_congr (fun m => by push_cast; ring_nf)
  rw [hM2, hP2, hM3neg, hP3neg]
  ring

theorem tendsto_gSharp_h3GC {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    Tendsto (fun N : ℕ => gSharp N x) atTop (nhds (h3GC x)) := by
  have hreal :
      Tendsto
        (fun N : ℕ =>
          (1 / 2 : ℝ) * deriv (HNcore N) x +
            (1 / 2 : ℝ) * deriv tailFn x)
        atTop
        (nhds ((1 / 2 : ℝ) * (∑' m : ℕ, dShift x m) +
          (1 / 2 : ℝ) * deriv tailFn x)) := by
    have h1 :
        Tendsto (fun N : ℕ => (1 / 2 : ℝ) * deriv (HNcore N) x)
          atTop (nhds ((1 / 2 : ℝ) * (∑' m : ℕ, dShift x m))) :=
      (tendsto_deriv_HNcore hs).const_mul (1 / 2 : ℝ)
    exact h1.add_const _
  rw [half_S_add_half_dtail_eq_h3G hs] at hreal
  have hcast :
      Tendsto (fun N : ℕ => gSharp N x) atTop
        (nhds ((h3G x : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto (h3G x)).comp hreal
    refine h.congr (fun N => ?_)
    simp [gSharp, Function.comp]
  simpa [h3GC] using hcast

theorem tendsto_gCes_h3GC {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    Tendsto (fun M : ℕ => gCes M x) atTop (nhds (h3GC x)) := by
  have hces :
      Tendsto
        (fun M : ℕ => ((M : ℝ)⁻¹ : ℝ) •
          ∑ N ∈ Finset.range M, gSharp N x)
        atTop (nhds (h3GC x)) :=
    (tendsto_gSharp_h3GC hs).cesaro_smul
  refine hces.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM1
  have hMpos : 0 < M := hM1
  rw [gCes_eq_average_gSharp M hMpos x, Complex.real_smul]
  push_cast
  ring

theorem sin_pi_ne_zero_ae :
    ∀ᵐ x : ℝ, Real.sin (Real.pi * x) ≠ 0 := by
  have hsub :
      {x : ℝ | ¬ Real.sin (Real.pi * x) ≠ 0} ⊆
        Set.range ((↑) : ℤ → ℝ) := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    rw [Real.sin_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have : x * Real.pi = (n : ℝ) * Real.pi := by
      rw [mul_comm x Real.pi, ← hn]
    exact (mul_right_cancel₀ hpi this).symm
  exact MeasureTheory.measure_mono_null hsub
    ((Set.countable_range _).measure_zero _)

theorem gCes_tendsto_h3GC_ae :
    ∀ᵐ x : ℝ, Tendsto (fun M : ℕ => gCes M x) atTop
      (nhds (h3GC x)) := by
  filter_upwards [sin_pi_ne_zero_ae] with x hx
  exact tendsto_gCes_h3GC hx

#print axioms tendsto_gSharp_h3GC
#print axioms tendsto_gCes_h3GC
#print axioms gCes_tendsto_h3GC_ae

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
