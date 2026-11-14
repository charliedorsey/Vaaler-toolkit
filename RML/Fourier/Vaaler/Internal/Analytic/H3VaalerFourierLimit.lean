module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerPointwiseLpIdentification
public import RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCoreFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.VaalerCesaroRemainderL2
open RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement

abbrev FourierL2 :
    Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
      Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

def RavgC (M : ℕ) (t : ℝ) : ℂ :=
  (VaalerCesaroRemainderL2.Ravg M t : ℂ)

theorem memLp_RavgC (M : ℕ) :
    MemLp (RavgC M) 2 (volume : Measure ℝ) := by
  unfold RavgC
  exact (VaalerCesaroRemainderL2.memLp_Ravg_two M).ofReal

theorem eLpNorm_RavgC_eq (M : ℕ) :
    eLpNorm (RavgC M) 2 (volume : Measure ℝ) =
      eLpNorm (VaalerCesaroRemainderL2.Ravg M) 2
        (volume : Measure ℝ) := by
  apply eLpNorm_congr_norm_ae
  · exact (memLp_RavgC M).aestronglyMeasurable
  · exact (VaalerCesaroRemainderL2.memLp_Ravg_two M).aestronglyMeasurable
  · filter_upwards with t
    simp [RavgC, Complex.norm_real, Real.norm_eq_abs]

theorem tendsto_eLpNorm_RavgC :
    Tendsto
      (fun M : ℕ => eLpNorm (RavgC M) 2 (volume : Measure ℝ))
      atTop (nhds (0 : ℝ≥0∞)) := by
  have heq :
      (fun M : ℕ => eLpNorm (RavgC M) 2 (volume : Measure ℝ)) =
        fun M : ℕ =>
          eLpNorm (VaalerCesaroRemainderL2.Ravg M) 2
            (volume : Measure ℝ) := by
    funext M
    exact eLpNorm_RavgC_eq M
  rw [heq]
  exact VaalerCesaroRemainderL2.tendsto_eLpNorm_Ravg

theorem tendsto_RavgC_Lp_zero :
    Tendsto
      (fun M : ℕ => (memLp_RavgC M).toLp (RavgC M))
      atTop
      (nhds (0 : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) := by
  let hz : MemLp (0 : ℝ → ℂ) 2 (volume : Measure ℝ) :=
    MemLp.zero'
  have hnorm :
      Tendsto
        (fun M : ℕ =>
          eLpNorm
            (⇑((memLp_RavgC M).toLp (RavgC M)) -
              (0 : ℝ → ℂ))
            2 (volume : Measure ℝ))
        atTop (nhds (0 : ℝ≥0∞)) := by
    refine (Filter.tendsto_congr (fun M => ?_)).mpr tendsto_eLpNorm_RavgC
    apply eLpNorm_congr_ae
    filter_upwards [(memLp_RavgC M).coeFn_toLp] with t ht
    simp [ht]
  have h := MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
    (f := fun M : ℕ => (memLp_RavgC M).toLp (RavgC M))
    (f_lim := (0 : ℝ → ℂ)) hz hnorm
  have hz0 : hz.toLp (0 : ℝ → ℂ) = 0 := MemLp.toLp_zero hz
  rw [hz0] at h
  exact h

def coreTarget (M : ℕ) (t : ℝ) : ℂ :=
  jPrincipalC t + RavgC M t

theorem memLp_jPrincipalC :
    MemLp jPrincipalC 2 (volume : Measure ℝ) := by
  unfold jPrincipalC
  exact h3VaalerJHatContC_memLp_two.sub memLp_jTailC_two

theorem memLp_coreTarget (M : ℕ) :
    MemLp (coreTarget M) 2 (volume : Measure ℝ) := by
  unfold coreTarget
  exact memLp_jPrincipalC.add (memLp_RavgC M)

theorem fourierLp_gCore_eq (M : ℕ) (hM : 0 < M) :
    FourierL2 ((memLp_gCore M).toLp (gCore M)) =
      (memLp_coreTarget M).toLp (coreTarget M) := by
  apply Lp.ext
  have hbridge :=
    RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ
      (integrable_gCore M) (memLp_gCore M)
  have hordinary :
      𝓕 (gCore M) =ᵐ[volume] coreTarget M := by
    have h := fourier_gCore_ae hM
    exact h.mono (fun t ht => by
      simpa [coreTarget, RavgC] using ht)
  exact hbridge.trans (hordinary.trans
    ((memLp_coreTarget M).coeFn_toLp).symm)

theorem toLp_gCes_eq_add (M : ℕ) :
    (memLp_gCes M).toLp (gCes M) =
      (memLp_gCore M).toLp (gCore M) +
        gTail_memLp_two.toLp gTail := by
  apply Lp.ext
  filter_upwards [
    (memLp_gCes M).coeFn_toLp,
    (memLp_gCore M).coeFn_toLp,
    gTail_memLp_two.coeFn_toLp,
    Lp.coeFn_add ((memLp_gCore M).toLp (gCore M))
      (gTail_memLp_two.toLp gTail)
  ] with x hces hcore htail hadd
  rw [hces, hadd]
  simp only [Pi.add_apply]
  rw [hcore, htail]
  exact congrFun (gCes_eq_gCore_add_gTail M) x

def fullTarget (M : ℕ) (t : ℝ) : ℂ :=
  h3VaalerJHatContC t + RavgC M t

theorem memLp_fullTarget (M : ℕ) :
    MemLp (fullTarget M) 2 (volume : Measure ℝ) := by
  unfold fullTarget
  exact h3VaalerJHatContC_memLp_two.add (memLp_RavgC M)

theorem coreTarget_add_jTail (M : ℕ) :
    coreTarget M + jTailC = fullTarget M := by
  funext t
  simp only [Pi.add_apply]
  unfold coreTarget fullTarget jPrincipalC
  ring

theorem toLp_coreTarget_add_jTail (M : ℕ) :
    (memLp_coreTarget M).toLp (coreTarget M) +
        memLp_jTailC_two.toLp jTailC =
      (memLp_fullTarget M).toLp (fullTarget M) := by
  apply Lp.ext
  filter_upwards [
    (memLp_coreTarget M).coeFn_toLp,
    memLp_jTailC_two.coeFn_toLp,
    (memLp_fullTarget M).coeFn_toLp,
    Lp.coeFn_add ((memLp_coreTarget M).toLp (coreTarget M))
      (memLp_jTailC_two.toLp jTailC)
  ] with t hcore htail hfull hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hcore, htail, hfull]
  exact congrFun (coreTarget_add_jTail M) t

theorem fourierLp_gCes_eq (M : ℕ) (hM : 0 < M) :
    FourierL2 ((memLp_gCes M).toLp (gCes M)) =
      (memLp_fullTarget M).toLp (fullTarget M) := by
  have hdec := congrArg FourierL2 (toLp_gCes_eq_add M)
  rw [map_add, fourierLp_gCore_eq M hM, tailFT_eq_jTail] at hdec
  exact hdec.trans (toLp_coreTarget_add_jTail M)

theorem fullTargetLp_eq_JHat_add_Ravg (M : ℕ) :
    (memLp_fullTarget M).toLp (fullTarget M) =
      h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC +
        (memLp_RavgC M).toLp (RavgC M) := by
  apply Lp.ext
  filter_upwards [
    (memLp_fullTarget M).coeFn_toLp,
    h3VaalerJHatContC_memLp_two.coeFn_toLp,
    (memLp_RavgC M).coeFn_toLp,
    Lp.coeFn_add
      (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)
      ((memLp_RavgC M).toLp (RavgC M))
  ] with t hfull hJ hR hadd
  rw [hfull, hadd]
  simp only [Pi.add_apply]
  rw [hJ, hR]
  rfl

theorem tendsto_fullTargetLp :
    Tendsto
      (fun M : ℕ => (memLp_fullTarget M).toLp (fullTarget M))
      atTop
      (nhds
        (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)) := by
  have hadd :
      Tendsto
        (fun M : ℕ =>
          h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC +
            (memLp_RavgC M).toLp (RavgC M))
        atTop
        (nhds
          (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC + 0)) :=
    tendsto_const_nhds.add tendsto_RavgC_Lp_zero
  have heq :
      (fun M : ℕ => (memLp_fullTarget M).toLp (fullTarget M)) =
        fun M : ℕ =>
          h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC +
            (memLp_RavgC M).toLp (RavgC M) := by
    funext M
    exact fullTargetLp_eq_JHat_add_Ravg M
  rw [heq]
  simpa using hadd

theorem fourierSideL2Limit :
    Tendsto
      (fun M : ℕ =>
        FourierL2 ((memLp_gCes M).toLp (gCes M)))
      atTop
      (nhds
        (h3VaalerJHatContC_memLp_two.toLp h3VaalerJHatContC)) := by
  refine tendsto_fullTargetLp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (fourierLp_gCes_eq M hM).symm

#print axioms tendsto_RavgC_Lp_zero
#print axioms fourierLp_gCore_eq
#print axioms fourierLp_gCes_eq
#print axioms fourierSideL2Limit

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFourierLimit
