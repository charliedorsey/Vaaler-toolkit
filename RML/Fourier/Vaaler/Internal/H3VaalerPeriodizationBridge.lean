module

public import RML.Fourier.Vaaler.Internal.H3VaalerSourceBridge
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier

noncomputable def h3VaalerSourceError (x : ℝ) : ℝ :=
  h3VaalerSign x - h3VaalerH x

noncomputable def h3VaalerSourceErrorAE (x : ℝ) : ℝ :=
  h3VaalerSign x -
    (Real.sin (Real.pi * x) / Real.pi) ^ 2 * h3VaalerCore x

theorem h3VaalerSign_measurable : Measurable h3VaalerSign := by
  unfold h3VaalerSign
  refine Measurable.ite measurableSet_Ioi measurable_const ?_
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem h3VaalerCore_measurable : Measurable h3VaalerCore := by
  unfold h3VaalerCore
  apply Measurable.add
  · apply Measurable.tsum
    intro n
    fun_prop
  · fun_prop

theorem h3VaalerSourceErrorAE_measurable :
    Measurable h3VaalerSourceErrorAE := by
  unfold h3VaalerSourceErrorAE
  have hs : Measurable (fun x : ℝ =>
      (Real.sin (Real.pi * x) / Real.pi) ^ 2) := by
    fun_prop
  exact h3VaalerSign_measurable.sub (hs.mul h3VaalerCore_measurable)

theorem h3VaalerSourceError_ae_eq :
    h3VaalerSourceError =ᵐ[volume] h3VaalerSourceErrorAE := by
  have hnull : volume (Set.range ((↑) : ℤ → ℝ)) = 0 := by
    exact (Set.countable_range ((↑) : ℤ → ℝ)).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
  unfold h3VaalerSourceError h3VaalerSourceErrorAE h3VaalerH
  rw [dif_neg]
  intro h
  rcases h with ⟨m, hm⟩
  exact hx ⟨m, hm.symm⟩

theorem h3VaalerSourceError_aestronglyMeasurable :
    AEStronglyMeasurable h3VaalerSourceError volume := by
  exact h3VaalerSourceErrorAE_measurable.aestronglyMeasurable.congr
    h3VaalerSourceError_ae_eq.symm

theorem h3VaalerSourceError_integrable :
    Integrable h3VaalerSourceError := by
  apply h3VaalerK_integrable.mono'
  · exact h3VaalerSourceError_aestronglyMeasurable
  · filter_upwards with x
    simpa [h3VaalerSourceError, h3VaalerSign, Real.norm_eq_abs] using
      h3Vaaler_sign_sub_abs_le_K x

theorem h3VaalerSourceError_neg (x : ℝ) :
    h3VaalerSourceError (-x) = -h3VaalerSourceError x := by
  unfold h3VaalerSourceError
  rw [h3VaalerH_neg, h3VaalerSign_eq_sign, h3VaalerSign_eq_sign,
    Real.sign_neg]
  ring

theorem integral_h3VaalerSourceError_eq_zero :
    (∫ x : ℝ, h3VaalerSourceError x) = 0 := by
  have hneg := MeasureTheory.integral_neg_eq_self h3VaalerSourceError volume
  have hfun : (fun x : ℝ => h3VaalerSourceError (-x)) =
      fun x : ℝ => -h3VaalerSourceError x := by
    funext x
    exact h3VaalerSourceError_neg x
  rw [hfun, integral_neg] at hneg
  linarith

theorem fourier_h3VaalerSourceError_zero :
    𝓕 (fun x : ℝ => (h3VaalerSourceError x : ℂ)) 0 = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, neg_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  rw [integral_complex_ofReal, integral_h3VaalerSourceError_eq_zero]
  simp

theorem h3ScaledVaalerError_eq_sourceError (J : ℕ) (x : ℝ) :
    h3ScaledVaalerError J x =
      (((J + 1 : ℕ) : ℝ)) *
        h3VaalerSourceError ((((J + 1 : ℕ) : ℝ)) * x) := by
  rfl

theorem h3ScaledVaalerError_integrable (J : ℕ) :
    Integrable (h3ScaledVaalerError J) := by
  let M : ℝ := (((J + 1 : ℕ) : ℝ))
  have hM : M ≠ 0 := by dsimp [M]; positivity
  have hc : Integrable (fun x : ℝ => h3VaalerSourceError (M * x)) :=
    h3VaalerSourceError_integrable.comp_mul_left' hM
  have hm : Integrable (fun x : ℝ => M * h3VaalerSourceError (M * x)) :=
    hc.const_mul M
  have hfun : h3ScaledVaalerError J =
      (fun x : ℝ => M * h3VaalerSourceError (M * x)) := by
    funext x
    exact h3ScaledVaalerError_eq_sourceError J x
  rwa [hfun]

theorem h3ScaledVaalerError_complex_integrable (J : ℕ) :
    Integrable (fun x : ℝ => (h3ScaledVaalerError J x : ℂ)) :=
  (h3ScaledVaalerError_integrable J).ofReal

theorem fourier_h3ScaledVaalerError_eq_source
    (J : ℕ) (t : ℝ) :
    𝓕 (fun x : ℝ => (h3ScaledVaalerError J x : ℂ)) t =
      𝓕 (fun u : ℝ => (h3VaalerSourceError u : ℂ))
        (t / (((J + 1 : ℕ) : ℝ))) := by
  let M : ℝ := (((J + 1 : ℕ) : ℝ))
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hM : M ≠ 0 := hMpos.ne'
  let g : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * Real.pi * u * (t / M) : ℝ) : ℂ) * Complex.I) •
      (h3VaalerSourceError u : ℂ)
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g M
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have hpoint : ∀ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I) •
          (h3ScaledVaalerError J x : ℂ) =
        (M : ℂ) * g (M * x) := by
    intro x
    rw [h3ScaledVaalerError_eq_sourceError]
    have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    have hexp :
        Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-2 * Real.pi * (M * x) * (t / M) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      field_simp [hMC]
    rw [hexp]
    dsimp [g, M]
    simp [smul_eq_mul]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, hchange]
  have habs : |M⁻¹| = M⁻¹ := abs_of_pos (inv_pos.mpr hMpos)
  rw [habs, Complex.real_smul]
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hcancel : (M : ℂ) * ((M⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [hMC]
  rw [← mul_assoc, hcancel, one_mul]

theorem h3ScaledVaalerError_interval_norm_summable (J : ℕ) :
    Summable fun n : ℤ =>
      ∫ x : ℝ in 0..1,
        ‖(h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)‖ := by
  have hsum := (h3ScaledVaalerError_complex_integrable J).norm
    |>.hasSum_intervalIntegral_comp_add_int
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hsum
  refine hneg.summable.congr ?_
  intro n
  simp [Function.comp_def, sub_eq_add_neg]

noncomputable def h3ScaledVaalerPeriodizedC (J : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℤ, (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)

noncomputable def h3FourierPhase (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * x * (k : ℝ) : ℝ) : ℂ) * Complex.I)

theorem h3FourierPhase_norm_one (k : ℤ) (x : ℝ) :
    ‖h3FourierPhase k x‖ = 1 := by
  unfold h3FourierPhase
  rw [Complex.norm_exp]
  simp

theorem h3FourierPhase_sub_intCast (k n : ℤ) (x : ℝ) :
    h3FourierPhase k (x - (n : ℝ)) = h3FourierPhase k x := by
  unfold h3FourierPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨n * k, ?_⟩
  push_cast
  ring

theorem h3_fourier_unit_eq_phase (k : ℤ) (x : ℝ) :
    fourier (T := (1 : ℝ)) (-k) (x : AddCircle (1 : ℝ)) = h3FourierPhase k x := by
  rw [fourier_coe_apply]
  unfold h3FourierPhase
  congr 1
  push_cast
  ring

theorem h3ScaledVaalerPeriodizedC_fourierCoeffOn
    (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (h3ScaledVaalerPeriodizedC J) k =
      𝓕 (fun x : ℝ => (h3ScaledVaalerError J x : ℂ)) (k : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let F : ℤ → ℝ → ℂ := fun n x =>
    h3FourierPhase k x * (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)
  have hFint : ∀ n : ℤ, Integrable (F n) μ := by
    intro n
    have herr : Integrable
        (fun x : ℝ => (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)) volume := by
      simpa [sub_eq_add_neg] using
        (h3ScaledVaalerError_complex_integrable J).comp_add_right (-(n : ℝ))
    dsimp [F, μ]
    change Integrable
      ((fun x : ℝ => h3FourierPhase k x) •
        (fun x : ℝ => (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)))
      (volume.restrict (Set.Ioc 0 1))
    apply (herr.restrict (s := Set.Ioc 0 1)).bdd_smul 1
    · exact (by
        unfold h3FourierPhase
        fun_prop : Continuous (fun x : ℝ => h3FourierPhase k x)) |>.aestronglyMeasurable
    · filter_upwards with x
      simpa [h3FourierPhase_norm_one]
  have hFnorm : Summable fun n : ℤ => ∫ x : ℝ, ‖F n x‖ ∂μ := by
    have hs := h3ScaledVaalerError_interval_norm_summable J
    refine hs.congr ?_
    intro n
    rw [show (∫ x : ℝ, ‖F n x‖ ∂μ) =
        ∫ x : ℝ in 0..1,
          ‖(h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)‖ by
      dsimp [μ, F]
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, h3FourierPhase_norm_one, one_mul]]
  have hinter := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFnorm
  let G : ℝ → ℂ := fun x =>
    h3FourierPhase k x * (h3ScaledVaalerError J x : ℂ)
  have hGint : Integrable G volume := by
    change Integrable
      ((fun x : ℝ => h3FourierPhase k x) •
        (fun x : ℝ => (h3ScaledVaalerError J x : ℂ))) volume
    apply (h3ScaledVaalerError_complex_integrable J).bdd_smul 1
    · exact (by
        unfold h3FourierPhase
        fun_prop : Continuous (fun x : ℝ => h3FourierPhase k x)) |>.aestronglyMeasurable
    · filter_upwards with x
      simpa [h3FourierPhase_norm_one]
  have hGsum := hGint.hasSum_intervalIntegral_comp_add_int
  have hGneg := (Equiv.neg ℤ).hasSum_iff.mpr hGsum
  have hGtsum :
      (∑' n : ℤ, ∫ x : ℝ in 0..1, G (x - (n : ℝ))) = ∫ x : ℝ, G x := by
    simpa [Function.comp_def, sub_eq_add_neg] using hGneg.tsum_eq
  have hterm : ∀ n : ℤ,
      (∫ x : ℝ, F n x ∂μ) = ∫ x : ℝ in 0..1, G (x - (n : ℝ)) := by
    intro n
    dsimp [μ]
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [F, G]
    rw [h3FourierPhase_sub_intCast]
  have hint : ∀ x : ℝ,
      fourier (T := (1 : ℝ)) (-k) (x : AddCircle (1 : ℝ)) •
          h3ScaledVaalerPeriodizedC J x =
        ∑' n : ℤ, F n x := by
    intro x
    rw [h3_fourier_unit_eq_phase]
    unfold h3ScaledVaalerPeriodizedC
    change h3FourierPhase k x *
        (∑' n : ℤ, (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)) =
      ∑' n : ℤ, F n x
    rw [← tsum_mul_left]
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div_one, one_smul]
  have hIntEq :
      (∫ x : ℝ in 0..1,
        fourier (T := ((1 : ℝ) - 0)) (-k) (x : AddCircle ((1 : ℝ) - 0)) •
          h3ScaledVaalerPeriodizedC J x) =
      ∫ x : ℝ in 0..1, ∑' n : ℤ, F n x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simpa using hint x
  refine hIntEq.trans ?_
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  change (∫ x : ℝ, ∑' n : ℤ, F n x ∂μ) = _
  rw [← hinter]
  simp_rw [hterm]
  rw [hGtsum]
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [G, h3FourierPhase]

noncomputable def h3VaalerPositiveTail (x : ℝ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2

theorem h3VaalerPositiveTail_continuousOn :
    ContinuousOn h3VaalerPositiveTail (Set.Ioi 0) := by
  have hu0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hu : Summable (fun n : ℕ =>
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
    simpa using (summable_nat_add_iff 1).2 hu0
  apply continuousOn_tsum
    (u := fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2)
  · intro n
    apply continuousOn_const.div
      ((continuousOn_id.add continuousOn_const).pow 2)
    intro x hx
    apply pow_ne_zero 2
    have hxpos : 0 < x := hx
    have hnnonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    exact ne_of_gt (add_pos_of_pos_of_nonneg hxpos hnnonneg)
  · exact hu
  · intro n x hx
    have hxpos : 0 < x := hx
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ x + ((n + 1 : ℕ) : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

noncomputable def h3VaalerPositiveDefect (x : ℝ) : ℝ :=
  (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
    (2 * h3VaalerPositiveTail x + 1 / x ^ 2 - 2 / x)

theorem h3VaalerPositiveDefect_continuousOn :
    ContinuousOn h3VaalerPositiveDefect (Set.Ioi 0) := by
  unfold h3VaalerPositiveDefect
  apply ContinuousOn.mul
  · fun_prop
  · apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact continuousOn_const.mul h3VaalerPositiveTail_continuousOn
      · apply continuousOn_const.div (continuousOn_id.pow 2)
        intro x hx
        change x ^ 2 ≠ 0
        exact pow_ne_zero 2 (ne_of_gt hx)
    · apply continuousOn_const.div continuousOn_id
      intro x hx
      exact ne_of_gt hx

theorem h3VaalerSourceError_eq_positiveDefect {x : ℝ} (hx : 0 < x) :
    h3VaalerSourceError x = h3VaalerPositiveDefect x := by
  by_cases hint : ∃ m : ℤ, x = (m : ℝ)
  · rcases hint with ⟨m, rfl⟩
    have hmpos : (0 : ℝ) < (m : ℝ) := hx
    have hsign : Real.sign (m : ℝ) = 1 := Real.sign_of_pos hmpos
    unfold h3VaalerSourceError h3VaalerPositiveDefect h3VaalerSign
    rw [h3VaalerH_intCast, hsign]
    rw [if_pos hmpos]
    have hsin : Real.sin (Real.pi * (m : ℝ)) = 0 := by
      rw [mul_comm]
      exact Real.sin_int_mul_pi m
    rw [hsin]
    norm_num
  · have h := h3VaalerH_one_minus_eq_kernel_defect hint
    unfold h3VaalerSourceError h3VaalerPositiveDefect h3VaalerPositiveTail h3VaalerSign
    rw [if_pos hx]
    exact h

theorem h3VaalerSourceError_continuousAt_of_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt h3VaalerSourceError x := by
  apply ContinuousAt.congr_of_eventuallyEq
    (h3VaalerPositiveDefect_continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds hx))
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact h3VaalerSourceError_eq_positiveDefect hy

theorem h3VaalerSourceError_continuousAt_of_neg {x : ℝ} (hx : x < 0) :
    ContinuousAt h3VaalerSourceError x := by
  have hpos : 0 < -x := neg_pos.mpr hx
  have hbase := h3VaalerSourceError_continuousAt_of_pos hpos
  have hcomp : ContinuousAt (fun y : ℝ => -h3VaalerSourceError (-y)) x := by
    exact (hbase.comp continuousAt_neg).neg
  simpa only [h3VaalerSourceError_neg, neg_neg] using hcomp

theorem h3VaalerSourceError_continuousAt_of_ne {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt h3VaalerSourceError x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · exact h3VaalerSourceError_continuousAt_of_neg hxneg
  · exact h3VaalerSourceError_continuousAt_of_pos hxpos

theorem h3ScaledVaalerError_continuousAt_of_ne
    (J : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (h3ScaledVaalerError J) x := by
  let M : ℝ := (((J + 1 : ℕ) : ℝ))
  have hM : M ≠ 0 := by dsimp [M]; positivity
  have hMx : M * x ≠ 0 := mul_ne_zero hM hx
  have hs := h3VaalerSourceError_continuousAt_of_ne hMx
  have hmul : ContinuousAt (fun y : ℝ => M * y) x := by fun_prop
  have hc : ContinuousAt (fun y : ℝ => h3VaalerSourceError (M * y)) x := by
    exact hs.comp hmul
  have hm : ContinuousAt (fun y : ℝ => M * h3VaalerSourceError (M * y)) x := by
    exact continuousAt_const.mul hc
  have hfun : h3ScaledVaalerError J =
      (fun y : ℝ => M * h3VaalerSourceError (M * y)) := by
    funext y
    exact h3ScaledVaalerError_eq_sourceError J y
  rwa [hfun]

noncomputable def h3RealDirichletSum (J : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (J + 1),
    Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) ^ k

theorem h3RealDirichletSum_norm_le (J : ℕ) (x : ℝ) :
    ‖h3RealDirichletSum J x‖ ≤ ((J + 1 : ℕ) : ℝ) := by
  unfold h3RealDirichletSum
  calc
    ‖∑ k ∈ Finset.range (J + 1),
        Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) ^ k‖
        ≤ ∑ k ∈ Finset.range (J + 1),
            ‖Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) ^ k‖ :=
      norm_sum_le _ _
    _ = ((J + 1 : ℕ) : ℝ) := by
      simp [Complex.norm_exp]

theorem h3RealFejerClosed_eq_dirichletNormSq
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    h3RealFejerClosed J x =
      (((J + 1 : ℕ) : ℝ))⁻¹ * ‖h3RealDirichletSum J x‖ ^ 2 := by
  let q : ℂ := Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)))
  have hq1 : q ≠ 1 := by
    intro hq
    rw [Complex.exp_eq_one_iff] at hq
    rcases hq with ⟨m, hm⟩
    apply hx
    refine ⟨m, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have him := congrArg Complex.im hm
    norm_num at him
    ring_nf at him
    nlinarith [Real.pi_pos]
  have hgeom :
      h3RealDirichletSum J x = (q ^ (J + 1) - 1) / (q - 1) := by
    unfold h3RealDirichletSum
    rw [show Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) = q by rfl]
    exact geom_sum_eq hq1 (J + 1)
  have hnum :
      ‖q ^ (J + 1) - 1‖ =
        |2 * Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ)) * x)| := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    have harg :
        ((J + 1 : ℕ) : ℂ) *
            (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) =
          Complex.I *
            (((2 * Real.pi * (((J + 1 : ℕ) : ℝ)) * x : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp only [Real.norm_eq_abs]
    congr 2
    ring
  have hden : ‖q - 1‖ = |2 * Real.sin (Real.pi * x)| := by
    dsimp [q]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    simp only [Real.norm_eq_abs]
    congr 2
    ring
  have hsin : Real.sin (Real.pi * x) ≠ 0 := by
    rw [Real.sin_ne_zero_iff]
    intro m hm
    apply hx
    refine ⟨m, ?_⟩
    nlinarith [Real.pi_pos]
  rw [hgeom, norm_div, hnum, hden]
  unfold h3RealFejerClosed
  have hM : (((J + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  conv_rhs =>
    rw [div_pow]
    rw [sq_abs (2 * Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ)) * x)),
      sq_abs (2 * Real.sin (Real.pi * x))]
  have harg : Real.pi * (((J + 1 : ℕ) : ℝ) * x) =
      Real.pi * (((J + 1 : ℕ) : ℝ)) * x := by ring
  rw [harg]
  field_simp [hM, hsin]

theorem h3RealFejerClosed_le (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    h3RealFejerClosed J x ≤ ((J + 1 : ℕ) : ℝ) := by
  rw [h3RealFejerClosed_eq_dirichletNormSq J hx]
  have hMpos : 0 < (((J + 1 : ℕ) : ℝ)) := by positivity
  have hnorm := h3RealDirichletSum_norm_le J x
  have hsq : ‖h3RealDirichletSum J x‖ ^ 2 ≤ (((J + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [norm_nonneg (h3RealDirichletSum J x)]
  calc
    (((J + 1 : ℕ) : ℝ))⁻¹ * ‖h3RealDirichletSum J x‖ ^ 2
        ≤ (((J + 1 : ℕ) : ℝ))⁻¹ * (((J + 1 : ℕ) : ℝ)) ^ 2 := by
          gcongr
    _ = ((J + 1 : ℕ) : ℝ) := by
      field_simp

theorem h3ScaledVaalerPeriodizedC_eq_ofReal
    (J : ℕ) (x : ℝ) :
    h3ScaledVaalerPeriodizedC J x =
      ((∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))) : ℂ) := by
  unfold h3ScaledVaalerPeriodizedC
  rfl

theorem h3ScaledVaalerPeriodizedC_norm_le_of_noninteger
    (J : ℕ) {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    ‖h3ScaledVaalerPeriodizedC J x‖ ≤ ((J + 1 : ℕ) : ℝ) := by
  calc
    ‖h3ScaledVaalerPeriodizedC J x‖ =
        ‖((∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))) : ℂ)‖ := by
          rw [h3ScaledVaalerPeriodizedC_eq_ofReal]
    _ = |∑' n : ℤ, h3ScaledVaalerError J (x - (n : ℝ))| := by
      rw [← Complex.ofReal_tsum]
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ h3RealFejerClosed J x := h3ScaledVaalerError_periodized_abs_le_closed J hx
    _ ≤ ((J + 1 : ℕ) : ℝ) := h3RealFejerClosed_le J hx

theorem h3ScaledVaalerPeriodizedC_aestronglyMeasurable_Ioc (J : ℕ) :
    AEStronglyMeasurable (h3ScaledVaalerPeriodizedC J)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply AEMeasurable.aestronglyMeasurable
  unfold h3ScaledVaalerPeriodizedC
  apply AEMeasurable.tsum
  intro n
  have hi : Integrable
      (fun x : ℝ => (h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)) volume := by
    simpa [sub_eq_add_neg] using
      (h3ScaledVaalerError_complex_integrable J).comp_add_right (-(n : ℝ))
  exact hi.aestronglyMeasurable.aemeasurable.mono_measure Measure.restrict_le_self

theorem h3ScaledVaalerPeriodizedC_memLp_two_Ioc (J : ℕ) :
    MemLp (h3ScaledVaalerPeriodizedC J) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply MeasureTheory.MemLp.of_bound
    (h3ScaledVaalerPeriodizedC_aestronglyMeasurable_Ioc J)
    (((J + 1 : ℕ) : ℝ))
  have hnull : volume (Set.range ((↑) : ℤ → ℝ)) = 0 := by
    exact (Set.countable_range ((↑) : ℤ → ℝ)).measure_zero volume
  have hAE0 : ∀ᵐ x : ℝ ∂volume, x ∉ Set.range ((↑) : ℤ → ℝ) :=
    compl_mem_ae_iff.mpr hnull
  have hAE : ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      x ∉ Set.range ((↑) : ℤ → ℝ) := hAE0.filter_mono ae_restrict_le
  filter_upwards [hAE] with x hx
  apply h3ScaledVaalerPeriodizedC_norm_le_of_noninteger J
  rintro ⟨m, hm⟩
  exact hx ⟨m, hm.symm⟩

theorem fourier_h3ScaledVaalerError_int
    (hCor7 : H3VaalerCor7TransformSpec)
    (J : ℕ) (k : ℤ) :
    𝓕 (fun x : ℝ => (h3ScaledVaalerError J x : ℂ)) (k : ℝ) =
      if k = 0 then 0 else
        (((J + 1 : ℕ) : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I * (k : ℂ)) *
          (1 - (h3VaalerJHat J k : ℂ)) := by
  rw [fourier_h3ScaledVaalerError_eq_source]
  by_cases hk : k = 0
  · subst k
    simp [fourier_h3VaalerSourceError_zero]
  · rw [if_neg hk]
    simpa [h3VaalerSourceError] using
      h3Vaaler_sampled_source_of_cor7 hCor7 J k hk

#print axioms fourier_h3ScaledVaalerError_int
#print axioms h3VaalerSourceError_integrable
#print axioms fourier_h3VaalerSourceError_zero
#print axioms h3ScaledVaalerError_integrable
#print axioms fourier_h3ScaledVaalerError_eq_source

end RML.Fourier.Vaaler.Internal
