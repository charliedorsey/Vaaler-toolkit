module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
public import RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
public import RML.Fourier.Vaaler.Internal.Analytic.SincSquare
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology SchwartzMap
open scoped FourierTransform ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.FejerTriangle
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
open RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous

def gTail (x : ℝ) : ℂ :=
  (((1 / 2 : ℝ) * deriv tailFn x : ℝ) : ℂ)

def jTail (t : ℝ) : ℝ :=
  if 1 ≤ |t| then 0 else if t = 0 then 0 else |t|

def jTailC (t : ℝ) : ℂ := (jTail t : ℂ)

theorem jTail_abs_le_one (t : ℝ) : |jTail t| ≤ 1 := by
  unfold jTail
  by_cases h1 : 1 ≤ |t|
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h0 : t = 0
    · simp [h0]
    · simp only [if_neg h0]
      rw [abs_abs]
      exact le_of_lt (not_le.mp h1)

theorem measurable_jTail : Measurable jTail := by
  unfold jTail
  apply Measurable.ite
  · exact measurableSet_le measurable_const continuous_abs.measurable
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_singleton 0 |>.preimage measurable_id |>.congr (by ext; simp)
    · exact measurable_const
    · exact continuous_abs.measurable

theorem aesm_jTailC :
    AEStronglyMeasurable jTailC (volume : Measure ℝ) :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable
    measurable_jTail.aestronglyMeasurable

theorem support_jTail_subset :
    Function.support jTail ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hmem
  apply ht
  rw [Set.mem_Icc, not_and_or] at hmem
  unfold jTail
  have h1 : 1 ≤ |t| := by
    rcases hmem with h | h
    · rw [not_le] at h
      rw [le_abs]
      right
      linarith
    · rw [not_le] at h
      rw [le_abs]
      left
      linarith
  simp [h1]

theorem integrable_jTailC :
    Integrable jTailC (volume : Measure ℝ) := by
  refine Integrable.mono'
    (g := Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℝ)))
    ?_ aesm_jTailC ?_
  · refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact integrableOn_const (by simp [Real.volume_Ioo])
  · refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases hmem : t ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hmem]
      unfold jTailC
      rw [Complex.norm_real]
      exact jTail_abs_le_one t
    · rw [Set.indicator_of_notMem hmem]
      have ht0 : jTail t = 0 := by
        by_contra hne
        exact hmem (support_jTail_subset (Function.mem_support.mpr hne))
      simp [jTailC, ht0]

theorem memLp_jTailC_two :
    MemLp jTailC 2 (volume : Measure ℝ) := by
  have hsupp : HasCompactSupport jTailC := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro t ht
    by_contra hne
    exact ht (support_jTail_subset (Function.mem_support.mpr (by simpa [jTailC] using hne)))
  refine hsupp.memLp_of_bound aesm_jTailC 1 ?_
  filter_upwards with t
  rw [jTailC, Complex.norm_real, Real.norm_eq_abs]
  exact jTail_abs_le_one t

theorem jTailC_even (t : ℝ) : jTailC (-t) = jTailC t := by
  unfold jTailC jTail
  rw [abs_neg]
  by_cases h1 : 1 ≤ |t|
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h0 : t = 0
    · simp [h0]
    · rw [if_neg (by simpa using h0), if_neg h0]

theorem h3VaalerK_even (x : ℝ) :
    h3VaalerK (-x) = h3VaalerK x := by
  unfold h3VaalerK
  by_cases h : x = 0
  · simp [h]
  · rw [if_neg (by simpa using h), if_neg h]
    rw [mul_neg, Real.sin_neg]
    field_simp

theorem deriv_h3VaalerK_odd (x : ℝ) :
    deriv h3VaalerK (-x) = - deriv h3VaalerK x := by
  have h :
      deriv (fun y => h3VaalerK (-y)) x =
        - deriv h3VaalerK (-x) := by
    simpa using (deriv_comp_neg h3VaalerK x)
  have he : (fun y => h3VaalerK (-y)) = h3VaalerK :=
    funext h3VaalerK_even
  rw [he] at h
  linarith

theorem gTail_even (x : ℝ) : gTail (-x) = gTail x := by
  rw [gTail, gTail, deriv_tailFn, deriv_tailFn,
    h3VaalerK_even, deriv_h3VaalerK_odd]
  push_cast
  ring

private def boxC (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) t

private theorem boxC_integrable :
    Integrable boxC (volume : Measure ℝ) := by
  unfold boxC
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact integrableOn_const (by simp [Real.volume_Ioo])

private theorem boxC_fourier_zero :
    𝓕 boxC 0 = (2 : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold boxC
  simp only [mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul]
  rw [integral_indicator_const (μ := volume)
    (s := Set.Ioo (-1 : ℝ) 1) (e := (1 : ℂ)) measurableSet_Ioo]
  rw [Real.volume_real_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

private theorem boxC_fourier_ne_zero {x : ℝ} (hx : x ≠ 0) :
    𝓕 boxC x =
      ((Real.sin (2 * Real.pi * x) / (Real.pi * x) : ℝ) : ℂ) := by
  let c : ℂ := (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  have hc : c ≠ 0 := by
    have hr : (-2 * Real.pi * x : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
  have hfour :
      𝓕 boxC x =
        ∫ t in (-1 : ℝ)..1, Complex.exp (c * (t : ℂ)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold boxC
    change
      (∫ v : ℝ,
        Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) •
          Set.indicator (Set.Ioo (-1 : ℝ) 1)
            (fun _ : ℝ => (1 : ℂ)) v) =
      ∫ t in (-1 : ℝ)..1, Complex.exp (c * (t : ℂ))
    have hind :
        (fun v : ℝ =>
          Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) •
            Set.indicator (Set.Ioo (-1 : ℝ) 1)
              (fun _ : ℝ => (1 : ℂ)) v) =
        Set.indicator (Set.Ioo (-1 : ℝ) 1)
          (fun v : ℝ => Complex.exp (c * (v : ℂ))) := by
      funext v
      by_cases hv : v ∈ Set.Ioo (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
        simp only [smul_eq_mul, mul_one]
        dsimp [c]
        congr 1
        push_cast
        ring
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
    rw [hind, integral_indicator measurableSet_Ioo]
    rw [← integral_Ioc_eq_integral_Ioo
      (f := fun t : ℝ => Complex.exp (c * (t : ℂ))) (μ := volume)]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [hfour, integral_exp_mul_complex hc]
  dsimp [c]
  rw [show (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * (1 : ℂ) =
      ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I by ring]
  rw [show (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * ((-1 : ℝ) : ℂ) =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  field_simp [hx, Real.pi_ne_zero, Complex.I_ne_zero]
  ring

private theorem boxC_fourier (x : ℝ) :
    𝓕 boxC x =
      ((if x = 0 then 2
        else Real.sin (2 * Real.pi * x) / (Real.pi * x) : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    rw [boxC_fourier_zero]
    norm_num
  · rw [boxC_fourier_ne_zero hx, if_neg hx]

private theorem deriv_h3VaalerK_zero :
    deriv h3VaalerK 0 = 0 := by
  have h := deriv_h3VaalerK_odd 0
  norm_num at h
  linarith [h]

private theorem gTail_eq_box_minus_h3VaalerK (x : ℝ) :
    gTail x =
      (((if x = 0 then 2
          else Real.sin (2 * Real.pi * x) / (Real.pi * x)) -
        h3VaalerK x : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    rw [gTail, deriv_tailFn, deriv_h3VaalerK_zero]
    simp [h3VaalerK]
    norm_num
  · rw [gTail, deriv_tailFn, deriv_h3VaalerK_offZero hx,
      if_neg hx]
    unfold h3VaalerK
    rw [if_neg hx]
    congr 1
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
      Real.sin_two_mul]
    field_simp [hx, Real.pi_ne_zero]
    ring

private theorem jTailC_eq_boxC_sub_fejerTriangle :
    jTailC =
      fun t : ℝ => boxC t - (fejerTriangle t : ℂ) := by
  funext t
  rw [jTailC, jTail, boxC]
  by_cases ht : |t| < 1
  · have hnot : ¬ 1 ≤ |t| := not_le.mpr ht
    rw [if_neg hnot]
    have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo]
      exact ⟨(abs_lt.mp ht).1, (abs_lt.mp ht).2⟩
    rw [Set.indicator_of_mem hmem]
    have htri : fejerTriangle t = 1 - |t| :=
      fejerTriangle_eq_one_sub_abs_of_abs_le_one (le_of_lt ht)
    by_cases ht0 : t = 0
    · rw [if_pos ht0, htri]
      simp [ht0]
    · rw [if_neg ht0, htri]
      push_cast
      ring
  · have hge : 1 ≤ |t| := le_of_not_gt ht
    rw [if_pos hge]
    have hnotmem : t ∉ Set.Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hge) (abs_lt.mpr hmem)
    rw [Set.indicator_of_notMem hnotmem,
      fejerTriangle_eq_zero_of_one_le_abs hge]
    norm_num

theorem fourierIntegral_jTailC_eq_gTail :
    𝓕 jTailC = gTail := by
  ext x
  have htriInt :
      Integrable (fun t : ℝ => (fejerTriangle t : ℂ))
        (volume : Measure ℝ) :=
    fejerTriangle_integrable.ofReal
  have hsplit :
      𝓕 jTailC x =
        𝓕 boxC x - 𝓕 (fun t : ℝ => (fejerTriangle t : ℂ)) x := by
    rw [jTailC_eq_boxC_sub_fejerTriangle]
    rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq]
    simp only [smul_sub]
    change
      (∫ v : ℝ,
        (Real.fourierChar (-(v * x))) • boxC v -
          (Real.fourierChar (-(v * x))) • (fejerTriangle v : ℂ)) =
      (∫ v : ℝ, (Real.fourierChar (-(v * x))) • boxC v) -
        ∫ v : ℝ, (Real.fourierChar (-(v * x))) • (fejerTriangle v : ℂ)
    rw [integral_sub]
    · simpa [Real.inner_apply, mul_comm] using
        (Real.fourierIntegral_convergent_iff x).2 boxC_integrable
    · simpa [Real.inner_apply, mul_comm] using
        (Real.fourierIntegral_convergent_iff x).2 htriInt
  rw [hsplit, boxC_fourier x,
    fourier_fejerTriangle_eq_sincSqPi x,
    ← h3VaalerK_eq_sincSqPi x]
  rw [← Complex.ofReal_sub]
  exact (gTail_eq_box_minus_h3VaalerK x).symm

private theorem fourierInvTransformL2_test_eq
    (T : Lp (α := ℝ) ℂ 2) (G : SchwartzMap ℝ ℂ) :
    ((𝓕⁻ T : Lp (α := ℝ) ℂ 2) : TemperedDistribution ℝ ℂ) G =
      ∫ x : ℝ, (𝓕⁻ G) x • (T : ℝ → ℂ) x := by
  rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq T]
  rw [TemperedDistribution.fourierInv_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

private theorem integral_fourierInv_schwartz_smul_eq
    (f : ℝ → ℂ) (hf : Integrable f) (g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (𝓕⁻ (fun y => g y)) x • f x) =
      ∫ xi : ℝ, (g xi) • (𝓕⁻ f) xi := by
  let gneg : SchwartzMap ℝ ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ))) g
  have hgneg : ∀ y : ℝ, gneg y = g (-y) := fun y => rfl
  calc
    (∫ x : ℝ, (𝓕⁻ (fun y => g y)) x • f x)
        = ∫ x : ℝ, (𝓕 (fun y : ℝ => (g : ℝ → ℂ) (-y))) x • f x := by
          rw [Real.fourierInv_eq_fourier_comp_neg
            (fun y : ℝ => (g : ℝ → ℂ) y)]
    _ = ∫ xi : ℝ, (g (-xi)) • (𝓕 f) xi := by
          rw [show (fun y : ℝ => (g : ℝ → ℂ) (-y)) =
              fun y : ℝ => gneg y by
            funext y
            exact (hgneg y).symm]
          simpa [hgneg] using
            integral_fourier_schwartz_smul_eq f hf gneg
    _ = ∫ xi : ℝ, (g xi) • (𝓕 f) (-xi) := by
          have h := integral_neg_eq_self
            (fun xi : ℝ => (g xi) * (𝓕 f) (-xi)) volume
          simp_rw [neg_neg] at h
          simpa [smul_eq_mul] using h
    _ = ∫ xi : ℝ, (g xi) • (𝓕⁻ f) xi := by
          refine integral_congr_ae ?_
          filter_upwards with xi
          rw [Real.fourierInv_eq_fourier_neg f xi]

private theorem continuous_fourierInv_of_integrable
    {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) := by
  have hcont : Continuous (fun x : ℝ => 𝓕 f (-x)) :=
    (continuous_fourier_of_integrable hf).comp continuous_neg
  convert hcont using 1
  ext x
  exact Real.fourierInv_eq_fourier_neg f x

theorem fourierIntegralInv_ae_eq_fourierTransformL2_symm
    {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (hf2.toLp f)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  set T : Lp (α := ℝ) ℂ 2 := hf2.toLp f with hT
  have hTf : (T : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hf1_li :
      LocallyIntegrable
        (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) :
          ℝ → ℂ) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hf2_li : LocallyIntegrable (𝓕⁻ f) volume :=
    (continuous_fourierInv_of_integrable hf).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hf1_li hf2_li ?_
  intro g g_smooth g_cpt
  have hG1 : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
    g_cpt.comp_left rfl
  have hG2 :
      ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by
    fun_prop
  set G : SchwartzMap ℝ ℂ := hG1.toSchwartzMap hG2 with hG
  have hGval : ∀ x, (G : ℝ → ℂ) x = ((g x : ℝ) : ℂ) :=
    fun x => rfl
  have hscal : ∀ (x : ℝ) (y : ℂ),
      (G : ℝ → ℂ) x • y = g x • y := by
    intro x y
    rw [hGval x]
    simp [Complex.real_smul]
  have hpair := fourierInvTransformL2_test_eq T G
  rw [MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
  calc
    (∫ x : ℝ, g x •
        (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) :
          ℝ → ℂ) x)
        = ∫ x : ℝ, (G : ℝ → ℂ) x •
            (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) :
              ℝ → ℂ) x :=
          integral_congr_ae
            (Filter.Eventually.of_forall
              (fun x => (hscal x _).symm))
    _ = ∫ x : ℝ, (𝓕⁻ G) x • (T : ℝ → ℂ) x := hpair
    _ = ∫ x : ℝ,
          (𝓕⁻ (fun y => (G : ℝ → ℂ) y)) x • (T : ℝ → ℂ) x := by
          rw [SchwartzMap.fourierInv_coe G]
    _ = ∫ x : ℝ,
          (𝓕⁻ (fun y => (G : ℝ → ℂ) y)) x • f x := by
          refine integral_congr_ae ?_
          filter_upwards [hTf] with x hx
          rw [hx]
    _ = ∫ xi : ℝ, (G : ℝ → ℂ) xi • (𝓕⁻ f) xi :=
          integral_fourierInv_schwartz_smul_eq f hf G
    _ = ∫ x : ℝ, g x • 𝓕⁻ f x :=
          integral_congr_ae
            (Filter.Eventually.of_forall (fun x => hscal x _))

theorem fourierInv_jTailC_eq_gTail :
    𝓕⁻ jTailC = gTail := by
  funext x
  rw [Real.fourierInv_eq_fourier_neg,
    fourierIntegral_jTailC_eq_gTail, gTail_even]

theorem gTail_memLp_two :
    MemLp gTail 2 (volume : Measure ℝ) := by
  let L : Lp (α := ℝ) ℂ 2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (memLp_jTailC_two.toLp jTailC)
  have hae : (⇑L : ℝ → ℂ) =ᵐ[volume] gTail := by
    dsimp [L]
    have h :=
      fourierIntegralInv_ae_eq_fourierTransformL2_symm
        integrable_jTailC memLp_jTailC_two
    rw [fourierInv_jTailC_eq_gTail] at h
    exact h
  exact (memLp_congr_ae hae).mp (Lp.memLp L)

theorem tailFT_eq_jTail :
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (gTail_memLp_two.toLp gTail) =
      memLp_jTailC_two.toLp jTailC := by
  let F := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  have hInvBridge :=
    fourierIntegralInv_ae_eq_fourierTransformL2_symm
      integrable_jTailC memLp_jTailC_two
  rw [fourierInv_jTailC_eq_gTail] at hInvBridge
  have hsymm_lp :
      F.symm (memLp_jTailC_two.toLp jTailC) =
        gTail_memLp_two.toLp gTail := by
    apply MeasureTheory.Lp.ext
    exact hInvBridge.trans (gTail_memLp_two.coeFn_toLp).symm
  have hkey := congrArg F hsymm_lp
  simpa [F] using hkey.symm

#print axioms fourierIntegral_jTailC_eq_gTail
#print axioms fourierIntegralInv_ae_eq_fourierTransformL2_symm
#print axioms gTail_memLp_two
#print axioms tailFT_eq_jTail

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
