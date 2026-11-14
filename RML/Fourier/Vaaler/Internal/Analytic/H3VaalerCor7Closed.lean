module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed
public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodizationBridge
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerInterpHContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare

theorem h3InterpBracket_eq_core (x : ℝ) :
    h3InterpBracket x = h3VaalerCore x := by
  have hc := h3VaalerCore_pos_index_form x
  have hs1 := h3_one_div_sub_succ_sq_summable x
  have hs2 := h3_one_div_add_succ_sq_summable x
  rw [hs1.tsum_sub hs2] at hc
  simpa only [h3InterpBracket, h3TailSum, one_div, div_eq_mul_inv,
    mul_comm, mul_one, inv_pow] using hc.symm

theorem h3InterpH_eq_h3VaalerH (x : ℝ) :
    h3InterpH x = h3VaalerH x := by
  classical
  by_cases hx : ∃ m : ℤ, x = (m : ℝ)
  · obtain ⟨m, rfl⟩ := hx
    rw [h3VaalerH_intCast]
    unfold h3InterpH
    have hs : Real.sin (Real.pi * (m : ℝ)) = 0 := by
      rw [mul_comm]
      exact Real.sin_int_mul_pi m
    rw [if_pos hs]
  · have hxrange : x ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨m, hm⟩
      exact hx ⟨m, hm.symm⟩
    have hs : Real.sin (Real.pi * x) ≠ 0 :=
      RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ.h3Sin_pi_mul_ne_zero_of_notMem hxrange
    unfold h3InterpH h3VaalerH
    rw [if_neg hs, dif_neg hx, h3InterpBracket_eq_core]

theorem h3VaalerJHatReal_eq_cont (t : ℝ) :
    h3VaalerJHatReal t = h3VaalerJHatCont t := by
  unfold h3VaalerJHatReal h3VaalerJHatCont
  by_cases ht0 : t = 0
  · subst t
    simp
  · by_cases hband : |t| < 1
    · rw [if_neg (not_le.mpr hband), if_neg ht0, if_neg ht0, if_pos hband]
    · have hge : 1 ≤ |t| := le_of_not_gt hband
      rw [if_pos hge, if_neg ht0, if_neg hband]

theorem h3VaalerSourceError_eq_sign_sub_interpH (x : ℝ) :
    h3VaalerSourceError x = Real.sign x - h3InterpH x := by
  unfold h3VaalerSourceError
  rw [h3VaalerSign_eq_sign, h3InterpH_eq_h3VaalerH]

theorem norm_h3VaalerSourceError_le_K (x : ℝ) :
    ‖(h3VaalerSourceError x : ℂ)‖ ≤ h3VaalerK x := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa [h3VaalerSourceError, h3VaalerSign] using
    h3Vaaler_sign_sub_abs_le_K x

def h3Echar (t x : ℝ) : ℂ :=
  Complex.exp ((-2 * Real.pi * Complex.I * t : ℂ) * (x : ℂ))

def h3EcharAntideriv (t x : ℝ) : ℂ :=
  h3Echar t x / (-2 * Real.pi * Complex.I * t : ℂ)

theorem norm_h3Echar (t x : ℝ) : ‖h3Echar t x‖ = 1 := by
  unfold h3Echar
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_h3Echar (t x : ℝ) :
    HasDerivAt (fun y : ℝ => h3Echar t y)
      (((-2 * Real.pi * Complex.I * t : ℂ)) * h3Echar t x) x := by
  have hlin : HasDerivAt
      (fun y : ℝ => (-2 * Real.pi * Complex.I * t : ℂ) * (y : ℂ))
      ((-2 * Real.pi * Complex.I * t : ℂ)) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.const_mul
      (-2 * Real.pi * Complex.I * t : ℂ))
  have hcomp := hlin.cexp
  unfold h3Echar
  convert hcomp using 1 <;> ring

theorem h3_neg_two_pi_I_t_ne_zero {t : ℝ} (ht : t ≠ 0) :
    (-2 * Real.pi * Complex.I * t : ℂ) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) htc

theorem hasDerivAt_h3EcharAntideriv {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => h3EcharAntideriv t y) (h3Echar t x) x := by
  have hc := h3_neg_two_pi_I_t_ne_zero ht
  have h := (hasDerivAt_h3Echar t x).div_const
    (-2 * Real.pi * Complex.I * t : ℂ)
  have hval :
      ((-2 * Real.pi * Complex.I * t : ℂ) * h3Echar t x) /
          (-2 * Real.pi * Complex.I * t : ℂ) = h3Echar t x := by
    rw [mul_comm, mul_div_assoc, div_self hc, mul_one]
  rw [hval] at h
  exact h

theorem h3Echar_eq_mathlib_kernel (t x : ℝ) :
    h3Echar t x =
      Complex.exp ((↑(-2 * Real.pi * x * t) : ℂ) * Complex.I) := by
  unfold h3Echar
  congr 1
  push_cast
  ring

theorem integral_sourceError_mul_echar_eq_fourier (t : ℝ) :
    (∫ x : ℝ, (h3VaalerSourceError x : ℂ) * h3Echar t x) =
      𝓕 (fun x : ℝ => (h3VaalerSourceError x : ℂ)) t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, mul_comm, h3Echar_eq_mathlib_kernel]

theorem hasDerivAt_sourceErrorC_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (h3VaalerSourceError y : ℂ))
      (-2 * ((h3VaalerJ x).re : ℂ)) x := by
  have h := (hasDerivAt_h3InterpH_two_reJ_global x).ofReal_comp.neg
  have hconst0 := h.add_const (1 : ℂ)
  refine (hconst0.congr_deriv ?_).congr_of_eventuallyEq ?_
  · push_cast
    ring
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [h3VaalerSourceError_eq_sign_sub_interpH, Real.sign_of_pos hy]
  push_cast
  simp only [Pi.neg_apply]
  ring

theorem hasDerivAt_sourceErrorC_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (fun y : ℝ => (h3VaalerSourceError y : ℂ))
      (-2 * ((h3VaalerJ x).re : ℂ)) x := by
  have h := (hasDerivAt_h3InterpH_two_reJ_global x).ofReal_comp.neg
  have hconst0 := h.sub_const (1 : ℂ)
  refine (hconst0.congr_deriv ?_).congr_of_eventuallyEq ?_
  · push_cast
    ring
  filter_upwards [Iio_mem_nhds hx] with y hy
  rw [h3VaalerSourceError_eq_sign_sub_interpH, Real.sign_of_neg hy]
  push_cast
  simp only [Pi.neg_apply]
  ring

theorem reJ_complex_ae_eq_h3GC :
    (fun x : ℝ => ((h3VaalerJ x).re : ℂ)) =ᵐ[volume] h3GC := by
  have hnull :
      volume (Set.range ((↑) : ℤ → ℝ)) = 0 :=
    (Set.countable_range ((↑) : ℤ → ℝ)).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
  have hcx := RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ.h3GC_eq_h3VaalerJ_offInt hx
  rw [← hcx]
  rfl

theorem fourier_reJ_eq_JHat (t : ℝ) :
    𝓕 (fun x : ℝ => ((h3VaalerJ x).re : ℂ)) t =
      (h3VaalerJHatCont t : ℂ) := by
  rw [Real.fourier_congr_ae reJ_complex_ae_eq_h3GC]
  exact GCFTeqJhat t

theorem reJ_complex_integrable :
    Integrable (fun x : ℝ => ((h3VaalerJ x).re : ℂ)) := by
  exact h3GC_integrable.congr reJ_complex_ae_eq_h3GC.symm

theorem continuous_h3Echar (t : ℝ) : Continuous (h3Echar t) := by
  unfold h3Echar
  fun_prop

theorem reJ_mul_echar_integrable (t : ℝ) :
    Integrable (fun x : ℝ => ((h3VaalerJ x).re : ℂ) * h3Echar t x) := by
  refine reJ_complex_integrable.mul_bdd (c := 1)
    (continuous_h3Echar t).aestronglyMeasurable ?_
  · filter_upwards with x
    rw [norm_h3Echar]

theorem two_reJ_mul_antideriv_integrable {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun x : ℝ =>
      (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) := by
  have h := (reJ_mul_echar_integrable t).const_mul (-2 : ℂ)
  have hd := h.div_const (-2 * Real.pi * Complex.I * t : ℂ)
  convert hd using 1
  funext x
  unfold h3EcharAntideriv
  ring

theorem pi_I_t_ne_zero {t : ℝ} (ht : t ≠ 0) :
    ((Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    (by exact_mod_cast ht)

theorem two_mul_antideriv_zero {t : ℝ} (ht : t ≠ 0) :
    2 * h3EcharAntideriv t 0 =
      -((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹ := by
  have hp := pi_I_t_ne_zero ht
  unfold h3EcharAntideriv h3Echar
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem integral_neg_two_reJ_mul_antideriv {t : ℝ} (ht : t ≠ 0) :
    (∫ x : ℝ,
      (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x)
      =
    ((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹ *
      (h3VaalerJHatCont t : ℂ) := by
  have hp := pi_I_t_ne_zero ht
  calc
    (∫ x : ℝ, (-2 * ((h3VaalerJ x).re : ℂ)) *
        h3EcharAntideriv t x)
        =
      ∫ x : ℝ,
        ((-2 : ℂ) / (-2 * Real.pi * Complex.I * (t : ℂ))) *
          (((h3VaalerJ x).re : ℂ) * h3Echar t x) := by
            apply integral_congr_ae
            filter_upwards with x
            unfold h3EcharAntideriv
            ring
    _ = ((-2 : ℂ) / (-2 * Real.pi * Complex.I * (t : ℂ))) *
        (∫ x : ℝ, ((h3VaalerJ x).re : ℂ) * h3Echar t x) := by
          rw [integral_const_mul]
    _ = ((-2 : ℂ) / (-2 * Real.pi * Complex.I * (t : ℂ))) *
        𝓕 (fun x : ℝ => ((h3VaalerJ x).re : ℂ)) t := by
          rw [Real.fourier_real_eq_integral_exp_smul]
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          rw [smul_eq_mul, mul_comm, h3Echar_eq_mathlib_kernel]
    _ = ((-2 : ℂ) / (-2 * Real.pi * Complex.I * (t : ℂ))) *
        (h3VaalerJHatCont t : ℂ) := by rw [fourier_reJ_eq_JHat]
    _ = ((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹ *
        (h3VaalerJHatCont t : ℂ) := by field_simp [hp]

theorem tendsto_h3VaalerK_atTop :
    Tendsto h3VaalerK atTop (𝓝 0) := by
  rw [h3VaalerK_eq_sincSqPi_fun]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => by
      dsimp [sincSqPi]; positivity)
  · exact Filter.Eventually.of_forall
      (fun x => sincSqPi_le_four_div_one_add_sq x)
  · have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have hone : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 hsq
    simpa [one_div] using
      ((tendsto_inv_atTop_zero.comp hone).const_mul (4 : ℝ))

theorem tendsto_h3VaalerK_atBot :
    Tendsto h3VaalerK atBot (𝓝 0) := by
  have h := tendsto_h3VaalerK_atTop.comp
    (tendsto_neg_atBot_atTop : Tendsto (fun x : ℝ => -x) atBot atTop)
  simpa only [Function.comp_def, h3VaalerK_neg] using h

theorem tendsto_sourceErrorC_atTop :
    Tendsto (fun x : ℝ => (h3VaalerSourceError x : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))
    (Filter.Eventually.of_forall (fun x => ?_))
    tendsto_h3VaalerK_atTop
  exact norm_h3VaalerSourceError_le_K x

theorem tendsto_sourceErrorC_atBot :
    Tendsto (fun x : ℝ => (h3VaalerSourceError x : ℂ)) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))
    (Filter.Eventually.of_forall (fun x => ?_))
    tendsto_h3VaalerK_atBot
  exact norm_h3VaalerSourceError_le_K x

theorem continuous_h3EcharAntideriv (t : ℝ) :
    Continuous (h3EcharAntideriv t) := by
  unfold h3EcharAntideriv h3Echar
  fun_prop

theorem tendsto_source_mul_antideriv_atTop {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x => (h3VaalerSourceError x : ℂ) *
      h3EcharAntideriv t x) atTop (𝓝 0) := by
  have hb : ∀ x : ℝ,
      ‖(h3VaalerSourceError x : ℂ) * h3EcharAntideriv t x‖ ≤
        h3VaalerK x * (2 * Real.pi * |t|)⁻¹ := by
    intro x
    rw [norm_mul]
    unfold h3EcharAntideriv
    rw [norm_div, norm_h3Echar]
    have hnorm :
        ‖(-2 * Real.pi * Complex.I * t : ℂ)‖ =
          2 * Real.pi * |t| := by
      rw [show (-2 * Real.pi * Complex.I * t : ℂ) =
          ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [show |(-2 * Real.pi * t : ℝ)| = 2 * Real.pi * |t| by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
        norm_num]
    rw [hnorm, one_div]
    apply mul_le_mul_of_nonneg_right
    · exact norm_h3VaalerSourceError_le_K x
    · positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall hb
  · simpa using tendsto_h3VaalerK_atTop.mul_const
      ((2 * Real.pi * |t|)⁻¹)

theorem tendsto_source_mul_antideriv_atBot {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x => (h3VaalerSourceError x : ℂ) *
      h3EcharAntideriv t x) atBot (𝓝 0) := by
  have hb : ∀ x : ℝ,
      ‖(h3VaalerSourceError x : ℂ) * h3EcharAntideriv t x‖ ≤
        h3VaalerK x * (2 * Real.pi * |t|)⁻¹ := by
    intro x
    rw [norm_mul]
    unfold h3EcharAntideriv
    rw [norm_div, norm_h3Echar]
    have hnorm :
        ‖(-2 * Real.pi * Complex.I * t : ℂ)‖ =
          2 * Real.pi * |t| := by
      rw [show (-2 * Real.pi * Complex.I * t : ℂ) =
          ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [show |(-2 * Real.pi * t : ℝ)| = 2 * Real.pi * |t| by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
        norm_num]
    rw [hnorm, one_div]
    apply mul_le_mul_of_nonneg_right
    · exact norm_h3VaalerSourceError_le_K x
    · positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall hb
  · simpa using tendsto_h3VaalerK_atBot.mul_const
      ((2 * Real.pi * |t|)⁻¹)

theorem tendsto_source_nhdsGT_zero :
    Tendsto (fun x : ℝ => (h3VaalerSourceError x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => (1 : ℂ) - (h3InterpH x : ℂ)) := by
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp h3InterpH_continuous)
  have h :
      Tendsto (fun x : ℝ => (1 : ℂ) - (h3InterpH x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℂ) - (h3InterpH 0 : ℂ))) :=
    hcont.continuousWithinAt.tendsto
  have heq :
      (fun x : ℝ => (1 : ℂ) - (h3InterpH x : ℂ))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => (h3VaalerSourceError x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mem_Ioi] at hx
    rw [h3VaalerSourceError_eq_sign_sub_interpH, Real.sign_of_pos hx]
    push_cast
    rfl
  simpa [RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed.h3InterpH_zero] using h.congr' heq

theorem tendsto_source_nhdsLT_zero :
    Tendsto (fun x : ℝ => (h3VaalerSourceError x : ℂ))
      (𝓝[<] (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => (-1 : ℂ) - (h3InterpH x : ℂ)) := by
    exact continuous_const.sub
      (Complex.continuous_ofReal.comp h3InterpH_continuous)
  have h :
      Tendsto (fun x : ℝ => (-1 : ℂ) - (h3InterpH x : ℂ))
        (𝓝[<] (0 : ℝ)) (𝓝 ((-1 : ℂ) - (h3InterpH 0 : ℂ))) :=
    hcont.continuousWithinAt.tendsto
  have heq :
      (fun x : ℝ => (-1 : ℂ) - (h3InterpH x : ℂ))
        =ᶠ[𝓝[<] (0 : ℝ)]
      (fun x : ℝ => (h3VaalerSourceError x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mem_Iio] at hx
    rw [h3VaalerSourceError_eq_sign_sub_interpH, Real.sign_of_neg hx]
    push_cast
    rfl
  simpa [RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobalClosed.h3InterpH_zero] using h.congr' heq

theorem tendsto_source_mul_antideriv_nhdsGT_zero (t : ℝ) :
    Tendsto (fun x => (h3VaalerSourceError x : ℂ) * h3EcharAntideriv t x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℂ) * h3EcharAntideriv t 0)) := by
  exact tendsto_source_nhdsGT_zero.mul
    (continuous_h3EcharAntideriv t).continuousWithinAt.tendsto

theorem tendsto_source_mul_antideriv_nhdsLT_zero (t : ℝ) :
    Tendsto (fun x => (h3VaalerSourceError x : ℂ) * h3EcharAntideriv t x)
      (𝓝[<] (0 : ℝ)) (𝓝 ((-1 : ℂ) * h3EcharAntideriv t 0)) := by
  exact tendsto_source_nhdsLT_zero.mul
    (continuous_h3EcharAntideriv t).continuousWithinAt.tendsto

theorem source_mul_echar_integrable (t : ℝ) :
    Integrable (fun x : ℝ =>
      (h3VaalerSourceError x : ℂ) * h3Echar t x) := by
  refine h3VaalerSourceError_integrable.ofReal.mul_bdd (c := 1)
    (continuous_h3Echar t).aestronglyMeasurable ?_
  · filter_upwards with x
    rw [norm_h3Echar]

theorem h3VaalerCor7TransformSpec_holds :
    H3VaalerCor7TransformSpec := by
  intro t ht
  change 𝓕 (fun x : ℝ => (h3VaalerSourceError x : ℂ)) t =
    (((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹) *
      (1 - (h3VaalerJHatReal t : ℂ))
  rw [← integral_sourceError_mul_echar_eq_fourier t]
  have hE := source_mul_echar_integrable t
  have hJ := two_reJ_mul_antideriv_integrable ht
  have hpos := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => (h3VaalerSourceError x : ℂ))
    (u' := fun x => -2 * ((h3VaalerJ x).re : ℂ))
    (v := h3EcharAntideriv t) (v' := h3Echar t)
    (fun x hx => hasDerivAt_sourceErrorC_pos hx)
    (fun x _ => hasDerivAt_h3EcharAntideriv ht x)
    hE.integrableOn hJ.integrableOn
    (tendsto_source_mul_antideriv_nhdsGT_zero t)
    (tendsto_source_mul_antideriv_atTop ht)
  have hneg := MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => (h3VaalerSourceError x : ℂ))
    (u' := fun x => -2 * ((h3VaalerJ x).re : ℂ))
    (v := h3EcharAntideriv t) (v' := h3Echar t)
    (fun x hx => hasDerivAt_sourceErrorC_neg hx)
    (fun x _ => hasDerivAt_h3EcharAntideriv ht x)
    hE.integrableOn hJ.integrableOn
    (tendsto_source_mul_antideriv_nhdsLT_zero t)
    (tendsto_source_mul_antideriv_atBot ht)
  have hsplitE :
      (∫ x in Iic (0 : ℝ), (h3VaalerSourceError x : ℂ) * h3Echar t x) +
          (∫ x in Ioi (0 : ℝ), (h3VaalerSourceError x : ℂ) * h3Echar t x)
        =
      ∫ x : ℝ, (h3VaalerSourceError x : ℂ) * h3Echar t x := by
    simpa only [compl_Iic] using
      (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hE)
  have hsplitJ :
      (∫ x in Iic (0 : ℝ),
        (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) +
          (∫ x in Ioi (0 : ℝ),
            (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x)
        =
      ∫ x : ℝ,
        (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x := by
    simpa only [compl_Iic] using
      (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hJ)
  calc
    (∫ x : ℝ, (h3VaalerSourceError x : ℂ) * h3Echar t x)
        =
      (∫ x in Iic (0 : ℝ),
        (h3VaalerSourceError x : ℂ) * h3Echar t x) +
      (∫ x in Ioi (0 : ℝ),
        (h3VaalerSourceError x : ℂ) * h3Echar t x) := hsplitE.symm
    _ = ((-1 : ℂ) * h3EcharAntideriv t 0 - 0 -
          ∫ x in Iic (0 : ℝ),
            (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) +
        (0 - (1 : ℂ) * h3EcharAntideriv t 0 -
          ∫ x in Ioi (0 : ℝ),
            (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) := by
          rw [hneg, hpos]
    _ = -2 * h3EcharAntideriv t 0 -
        ((∫ x in Iic (0 : ℝ),
          (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) +
         ∫ x in Ioi (0 : ℝ),
          (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) := by
          ring
    _ = -2 * h3EcharAntideriv t 0 -
        (∫ x : ℝ,
          (-2 * ((h3VaalerJ x).re : ℂ)) * h3EcharAntideriv t x) := by
          rw [hsplitJ]
    _ = (((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹) *
        (1 - (h3VaalerJHatReal t : ℂ)) := by
          rw [show -2 * h3EcharAntideriv t 0 =
            ((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹ by
              calc
                -2 * h3EcharAntideriv t 0 =
                    -(2 * h3EcharAntideriv t 0) := by ring
                _ = -(-((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹) := by
                    rw [two_mul_antideriv_zero ht]
                _ = ((Real.pi : ℂ) * Complex.I * (t : ℂ))⁻¹ := by ring]
          rw [integral_neg_two_reJ_mul_antideriv ht,
            h3VaalerJHatReal_eq_cont]
          ring

#print axioms h3VaalerCor7TransformSpec_holds

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed
