module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDerivLp
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
public import RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDerivLp
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
open RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement

def JF (x : ℝ) : ℂ := 𝓕 h3VaalerJHatContC x

def dJF (x : ℝ) : ℂ := 𝓕 dJC x

theorem JF_memLp_two :
    MemLp JF 2 (volume : Measure ℝ) := by
  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
      (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)
  have hT : MemLp (⇑T : ℝ → ℂ) 2 (volume : Measure ℝ) := Lp.memLp T
  have hbridge :=
    RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ
      h3VaalerJHatContC_integrable h3VaalerJHatContC_memLp_two
  have hae : (⇑T : ℝ → ℂ) =ᵐ[volume] JF := by
    exact hbridge.mono (fun x hx => by simpa [T, JF] using hx)
  exact (memLp_congr_ae hae).mp hT

theorem dJF_memLp_two :
    MemLp dJF 2 (volume : Measure ℝ) := by
  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
      (dJC_memLp_two.toLp dJC)
  have hT : MemLp (⇑T : ℝ → ℂ) 2 (volume : Measure ℝ) := Lp.memLp T
  have hbridge :=
    RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ
      dJC_integrable dJC_memLp_two
  have hae : (⇑T : ℝ → ℂ) =ᵐ[volume] dJF := by
    exact hbridge.mono (fun x hx => by simpa [T, dJF] using hx)
  exact (memLp_congr_ae hae).mp hT

theorem fourier_deriv_JHat :
    dJF =
      fun x : ℝ => (2 * Real.pi * Complex.I * x) • JF x := by
  have h :=
    Real.fourier_deriv
      h3VaalerJHatContC_integrable
      differentiable_h3VaalerJHatContC
      deriv_h3VaalerJHatContC_integrable
  have hder : deriv h3VaalerJHatContC = dJC := by
    funext x
    exact deriv_h3VaalerJHatContC x
  rw [hder] at h
  funext x
  have hx := congrFun h x
  simpa [dJF, JF] using hx

def xJF (x : ℝ) : ℂ := (x : ℂ) * JF x

theorem xJF_eq_const_mul_dJF :
    xJF =
      fun x : ℝ => ((2 * Real.pi : ℂ) * Complex.I)⁻¹ * dJF x := by
  funext x
  have h := congrFun fourier_deriv_JHat x
  simp only [smul_eq_mul] at h
  unfold xJF
  have hc : ((2 * Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [h]
  field_simp [hc]

theorem xJF_memLp_two :
    MemLp xJF 2 (volume : Measure ℝ) := by
  rw [xJF_eq_const_mul_dJF]
  exact dJF_memLp_two.const_mul (((2 * Real.pi : ℂ) * Complex.I)⁻¹)

def weightedJF (x : ℝ) : ℂ :=
  (Real.sqrt (1 + x ^ 2) : ℂ) * JF x

theorem weightedJF_aestronglyMeasurable :
    AEStronglyMeasurable weightedJF (volume : Measure ℝ) := by
  have hF : AEStronglyMeasurable JF (volume : Measure ℝ) :=
    JF_memLp_two.aestronglyMeasurable
  have hw : StronglyMeasurable
      (fun x : ℝ => ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))).stronglyMeasurable
  exact hw.aestronglyMeasurable.mul hF

theorem weightedJF_sq_norm_eq (x : ℝ) :
    ‖weightedJF x‖ ^ 2 =
      ‖JF x‖ ^ 2 + ‖xJF x‖ ^ 2 := by
  unfold weightedJF xJF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsqrt : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  rw [abs_of_nonneg hsqrt]
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [mul_pow, hsq]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow]
  have habsx : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [habsx]
  ring

theorem weightedJF_memLp_two :
    MemLp weightedJF 2 (volume : Measure ℝ) := by
  have hFint :
      Integrable (fun x : ℝ => ‖JF x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm JF_memLp_two.aestronglyMeasurable).mp JF_memLp_two
  have hxint :
      Integrable (fun x : ℝ => ‖xJF x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm xJF_memLp_two.aestronglyMeasurable).mp xJF_memLp_two
  refine (memLp_two_iff_integrable_sq_norm weightedJF_aestronglyMeasurable).mpr ?_
  have hsum := hFint.add hxint
  have heq : (fun x : ℝ => ‖weightedJF x‖ ^ 2) =
      fun x : ℝ => ‖JF x‖ ^ 2 + ‖xJF x‖ ^ 2 := by
    funext x
    exact weightedJF_sq_norm_eq x
  rw [heq]
  exact hsum

def invWeight (x : ℝ) : ℂ :=
  ((Real.sqrt (1 + x ^ 2))⁻¹ : ℝ)

theorem invWeight_aestronglyMeasurable :
    AEStronglyMeasurable invWeight (volume : Measure ℝ) := by
  have hbase : Continuous (fun x : ℝ => Real.sqrt (1 + x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
  have hreal : Continuous (fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹) :=
    hbase.inv₀ (fun x => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hcont : Continuous invWeight := by
    unfold invWeight
    exact Complex.continuous_ofReal.comp hreal
  exact hcont.aestronglyMeasurable

theorem invWeight_sq_norm_eq (x : ℝ) :
    ‖invWeight x‖ ^ 2 = (1 + x ^ 2)⁻¹ := by
  unfold invWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv]
  have hsqrt : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  rw [abs_of_nonneg hsqrt, inv_pow]
  rw [Real.sq_sqrt (by positivity)]

theorem invWeight_memLp_two :
    MemLp invWeight 2 (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq_norm invWeight_aestronglyMeasurable).mpr ?_
  have heq : (fun x : ℝ => ‖invWeight x‖ ^ 2) =
      fun x : ℝ => (1 + x ^ 2)⁻¹ := by
    funext x
    exact invWeight_sq_norm_eq x
  rw [heq]
  exact integrable_inv_one_add_sq

theorem invWeight_mul_weightedJF (x : ℝ) :
    invWeight x * weightedJF x = JF x := by
  unfold invWeight weightedJF
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsne : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hspos
  push_cast
  field_simp [hsne]

theorem JF_integrable :
    Integrable JF (volume : Measure ℝ) := by
  have hprod :
      Integrable (invWeight * weightedJF) (volume : Measure ℝ) :=
    invWeight_memLp_two.integrable_mul weightedJF_memLp_two
  have heq : invWeight * weightedJF = JF := by
    funext x
    exact invWeight_mul_weightedJF x
  rwa [heq] at hprod

theorem JHat_even_C (t : ℝ) :
    h3VaalerJHatContC (-t) = h3VaalerJHatContC t := by
  simp [h3VaalerJHatContC, h3VaalerJHatCont_neg]

theorem fourierInv_JHat_eq_JF :
    𝓕⁻ h3VaalerJHatContC = JF := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  have heq :
      (fun x : ℝ => h3VaalerJHatContC (-x)) =
        h3VaalerJHatContC := by
    funext x
    exact JHat_even_C x
  rw [heq]
  rfl

theorem fourierInv_JHat_integrable :
    Integrable (𝓕⁻ h3VaalerJHatContC) (volume : Measure ℝ) := by
  rw [fourierInv_JHat_eq_JF]
  exact JF_integrable

theorem fourierInv_JHat_ae_eq_h3GC :
    𝓕⁻ h3VaalerJHatContC =ᵐ[volume]
      RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous.h3GC := by
  have hInvLp :=
    RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier.fourierIntegralInv_ae_eq_fourierTransformL2_symm
      h3VaalerJHatContC_integrable h3VaalerJHatContC_memLp_two
  have hGC :=
    RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification.inverseJ_ae_eq_h3GC
      RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp.memLp_gCes
      RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit.fourierSideL2Limit
  exact hInvLp.symm.trans hGC

theorem h3GC_integrable :
    Integrable RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous.h3GC
      (volume : Measure ℝ) := by
  exact fourierInv_JHat_integrable.congr fourierInv_JHat_ae_eq_h3GC

#print axioms JF_memLp_two
#print axioms xJF_memLp_two
#print axioms weightedJF_memLp_two
#print axioms JF_integrable
#print axioms h3GC_integrable

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable
