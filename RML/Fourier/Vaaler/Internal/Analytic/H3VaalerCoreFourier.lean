module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFiniteExpSum
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroDirichletSum
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
public import RML.Fourier.Vaaler.Internal.Analytic.VaalerCesaroRemainderL2
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCoreFourier

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.FejerTriangle
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivIntegrable
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerFiniteExpSum
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroDirichletSum
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier

def echar (t x : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * t * x)

theorem echar_add (t a b : ℝ) :
    echar t (a + b) = echar t a * echar t b := by
  unfold echar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem h3VaalerK_shift_FT (t a : ℝ) :
    (∫ x : ℝ, (h3VaalerK (x - a) : ℂ) * echar t x) =
      echar t a * ∫ y : ℝ, (h3VaalerK y : ℂ) * echar t y := by
  have hself := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => (h3VaalerK x : ℂ) * echar t (x + a)) a
  have hlhs :
      (∫ x : ℝ,
        (fun x : ℝ => (h3VaalerK x : ℂ) * echar t (x + a)) (x - a)) =
      ∫ x : ℝ, (h3VaalerK (x - a) : ℂ) * echar t x := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only
    rw [show (x - a) + a = x by ring]
  rw [hlhs] at hself
  rw [hself, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [echar_add]
  ring

theorem h3VaalerK_FT_eq (t : ℝ) :
    (∫ y : ℝ, (h3VaalerK y : ℂ) * echar t y) =
      (fejerTriangle t : ℂ) := by
  have hker : ∀ y : ℝ,
      echar t y =
        Complex.exp ((↑(-2 * Real.pi * ⟪y, t⟫) * Complex.I)) := by
    intro y
    unfold echar
    rw [Real.inner_apply]
    congr 1
    push_cast
    ring
  have hfour := congrFun fourier_h3VaalerK_eq_fejerTriangle t
  rw [Real.fourier_eq'] at hfour
  rw [← hfour]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change (h3VaalerK y : ℂ) * echar t y =
    Complex.exp ((↑(-2 * Real.pi * ⟪y, t⟫) * Complex.I)) • (h3VaalerK y : ℂ)
  rw [hker]
  simp [smul_eq_mul]
  ring

theorem h3VaalerK_shift_FT_value (t a : ℝ) :
    (∫ x : ℝ, (h3VaalerK (x - a) : ℂ) * echar t x) =
      echar t a * (fejerTriangle t : ℂ) := by
  rw [h3VaalerK_shift_FT, h3VaalerK_FT_eq]

theorem integrable_h3VaalerK_shift_echar (t a : ℝ) :
    Integrable (fun x : ℝ => (h3VaalerK (x - a) : ℂ) * echar t x) := by
  have hKshift :
      Integrable (fun x : ℝ => h3VaalerK (x - a)) :=
    h3VaalerK_integrable.comp_sub_right a
  refine (hKshift.ofReal).mul_bdd (c := 1) ?_ ?_
  · exact (by unfold echar; fun_prop :
      Continuous (fun x : ℝ => echar t x)).aestronglyMeasurable
  · filter_upwards with x
    unfold echar
    rw [show (-2 : ℂ) * Real.pi * Complex.I * t * x =
        ((-2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
      Complex.norm_exp_ofReal_mul_I]

theorem HNcore_FT (N : ℕ) (t : ℝ) :
    (∫ z : ℝ, (HNcore N z : ℂ) * echar t z) =
      (fejerTriangle t : ℂ) * sgnExpSum N t := by
  have hcast :
      (fun z : ℝ => (HNcore N z : ℂ) * echar t z) =
        fun z : ℝ => ∑ m ∈ Finset.range N,
          (((h3VaalerK (z - ((m : ℝ) + 1)) : ℂ) * echar t z) -
            ((h3VaalerK (z + ((m : ℝ) + 1)) : ℂ) * echar t z)) := by
    funext z
    unfold HNcore
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => by ring)
  rw [hcast]
  have hadd_eq : ∀ c : ℝ,
      (fun z : ℝ => (h3VaalerK (z + c) : ℂ) * echar t z) =
        (fun z : ℝ => (h3VaalerK (z - (-c)) : ℂ) * echar t z) := by
    intro c
    funext z
    rw [sub_neg_eq_add]
  have hint : ∀ m ∈ Finset.range N,
      Integrable (fun z : ℝ =>
        ((h3VaalerK (z - ((m : ℝ) + 1)) : ℂ) * echar t z) -
          ((h3VaalerK (z + ((m : ℝ) + 1)) : ℂ) * echar t z)) := by
    intro m _
    refine (integrable_h3VaalerK_shift_echar t ((m : ℝ) + 1)).sub ?_
    rw [hadd_eq ((m : ℝ) + 1)]
    exact integrable_h3VaalerK_shift_echar t (-((m : ℝ) + 1))
  rw [MeasureTheory.integral_finsetSum _ hint]
  have heval : ∀ m ∈ Finset.range N,
      (∫ z : ℝ,
        (((h3VaalerK (z - ((m : ℝ) + 1)) : ℂ) * echar t z) -
          ((h3VaalerK (z + ((m : ℝ) + 1)) : ℂ) * echar t z))) =
        (fejerTriangle t : ℂ) *
          (echarC (-(((m : ℝ) + 1) * t)) -
            echarC (((m : ℝ) + 1) * t)) := by
    intro m _
    rw [MeasureTheory.integral_sub
      (integrable_h3VaalerK_shift_echar t ((m : ℝ) + 1))
      (by
        rw [hadd_eq ((m : ℝ) + 1)]
        exact integrable_h3VaalerK_shift_echar t (-((m : ℝ) + 1)))]
    rw [h3VaalerK_shift_FT_value t ((m : ℝ) + 1),
      hadd_eq ((m : ℝ) + 1),
      h3VaalerK_shift_FT_value t (-((m : ℝ) + 1))]
    have hechar : ∀ a : ℝ, echar t a = echarC (-(a * t)) := by
      intro a
      unfold echar echarC
      congr 1
      push_cast
      ring
    rw [hechar, hechar]
    ring
  rw [Finset.sum_congr rfl heval, ← Finset.mul_sum]
  congr 1
  unfold sgnExpSum
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hc : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hc]

theorem HNcore_FT_eq_triangle_cot {N : ℕ} {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∫ z : ℝ, (HNcore N z : ℂ) * echar t z) =
      (fejerTriangle t : ℂ) *
        (-Complex.I * cotC t +
          Complex.I *
            ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
              (Real.sin (Real.pi * t) : ℂ))) := by
  rw [HNcore_FT, sgnExpSum_eq ht]

theorem echar_eq_fourierKernel (t v : ℝ) :
    Complex.exp (((-2 * Real.pi * ⟪v, t⟫) : ℝ) * Complex.I) = echar t v := by
  rw [Real.inner_apply]
  unfold echar
  congr 1
  push_cast
  ring

theorem integral_mul_echar_eq_fourier (f : ℝ → ℂ) (t : ℝ) :
    (∫ v : ℝ, f v * echar t v) = 𝓕 f t := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [smul_eq_mul]
  rw [← echar_eq_fourierKernel t v]
  ring

theorem halfDeriv_FT_eq_mul {f g : ℝ → ℂ}
    (hf : Integrable f) (hf' : Differentiable ℝ f)
    (hderiv : Integrable (deriv f))
    (hhalf : deriv f = fun v => 2 * g v) (t : ℝ) :
    (∫ v : ℝ, g v * echar t v) =
      (Real.pi * Complex.I * t : ℂ) *
        (∫ v : ℝ, f v * echar t v) := by
  have hg : Integrable g := by
    have h : g = fun v => (1 / 2 : ℂ) * deriv f v := by
      funext v
      rw [hhalf]
      ring
    rw [h]
    exact hderiv.const_mul _
  rw [integral_mul_echar_eq_fourier g t,
    integral_mul_echar_eq_fourier f t]
  have hFD := fourier_deriv hf hf' hderiv
  have hFDg :
      𝓕 (deriv f) t = (2 : ℂ) * 𝓕 g t := by
    rw [← integral_mul_echar_eq_fourier (deriv f) t,
      ← integral_mul_echar_eq_fourier g t]
    rw [hhalf, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae
      (Filter.Eventually.of_forall (fun v => by ring))
  have hFDt :
      𝓕 (deriv f) t =
        (2 * Real.pi * Complex.I * t) * 𝓕 f t := by
    rw [hFD]
    simp [smul_eq_mul]
  have keyt :
      (2 : ℂ) * 𝓕 g t =
        (2 * Real.pi * Complex.I * t) * 𝓕 f t := by
    rw [← hFDg, hFDt]
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  rw [keyt]
  ring

def HNcoreC (N : ℕ) (x : ℝ) : ℂ := (HNcore N x : ℂ)

theorem integrable_HNcoreC (N : ℕ) :
    Integrable (HNcoreC N) (volume : Measure ℝ) := by
  have hfun :
      HNcoreC N =
        fun x : ℝ => ∑ m ∈ Finset.range N,
          ((h3VaalerK (x - ((m : ℝ) + 1)) : ℂ) -
            (h3VaalerK (x + ((m : ℝ) + 1)) : ℂ)) := by
    funext x
    simp only [HNcoreC, HNcore]
    push_cast
    rfl
  rw [hfun]
  refine MeasureTheory.integrable_finsetSum _ (fun m _ => ?_)
  refine ((h3VaalerK_integrable.comp_sub_right ((m : ℝ) + 1)).ofReal).sub ?_
  have hbaseR : Integrable (fun x : ℝ =>
      h3VaalerK (x - (-((m : ℝ) + 1)))) :=
    h3VaalerK_integrable.comp_sub_right (-((m : ℝ) + 1))
  have heq : (fun x : ℝ => h3VaalerK (x - (-((m : ℝ) + 1)))) =
      fun x : ℝ => h3VaalerK (x + ((m : ℝ) + 1)) := by
    funext x
    congr 1
    ring
  rw [heq] at hbaseR
  exact hbaseR.ofReal

theorem differentiable_HNcoreC (N : ℕ) :
    Differentiable ℝ (HNcoreC N) := by
  intro x
  have hR : HasDerivAt (HNcore N) (deriv (HNcore N) x) x :=
    ((contDiff_HNcore N).differentiable (by simp)).differentiableAt.hasDerivAt
  exact hR.ofReal_comp.differentiableAt

theorem deriv_HNcoreC (N : ℕ) (x : ℝ) :
    deriv (HNcoreC N) x = ((deriv (HNcore N) x : ℝ) : ℂ) := by
  unfold HNcoreC
  have hR :
      HasDerivAt (HNcore N) (deriv (HNcore N) x) x :=
    ((contDiff_HNcore N).differentiable (by simp)).differentiableAt.hasDerivAt
  exact hR.ofReal_comp.deriv

theorem integrable_deriv_HNcoreC (N : ℕ) :
    Integrable (deriv (HNcoreC N)) (volume : Measure ℝ) := by
  have hpoint :
      deriv (HNcoreC N) =
        fun x : ℝ => ∑ m ∈ Finset.range N,
          (((deriv h3VaalerK (x - ((m : ℝ) + 1)) : ℝ) : ℂ) -
            ((deriv h3VaalerK (x + ((m : ℝ) + 1)) : ℝ) : ℂ)) := by
    funext x
    rw [deriv_HNcoreC, deriv_HNcore_eq]
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold dShift
    push_cast
    rfl
  rw [hpoint]
  refine MeasureTheory.integrable_finsetSum _ (fun m _ => ?_)
  have hsub :
      Integrable (fun x : ℝ =>
        deriv h3VaalerK (x - ((m : ℝ) + 1))) :=
    integrable_deriv_h3VaalerK.comp_sub_right ((m : ℝ) + 1)
  have hadd :
      Integrable (fun x : ℝ =>
        deriv h3VaalerK (x + ((m : ℝ) + 1))) := by
    have heq :
        (fun x : ℝ => deriv h3VaalerK (x + ((m : ℝ) + 1))) =
          fun x : ℝ =>
            deriv h3VaalerK (x - (-((m : ℝ) + 1))) := by
      funext x
      rw [sub_neg_eq_add]
    rw [heq]
    exact integrable_deriv_h3VaalerK.comp_sub_right (-((m : ℝ) + 1))
  exact hsub.ofReal.sub hadd.ofReal

def halfDerivHN (N : ℕ) (x : ℝ) : ℂ :=
  (((1 / 2 : ℝ) * deriv (HNcore N) x : ℝ) : ℂ)

theorem integrable_halfDerivHN (N : ℕ) :
    Integrable (halfDerivHN N) (volume : Measure ℝ) := by
  have h :
      halfDerivHN N =
        fun x : ℝ => (1 / 2 : ℂ) * deriv (HNcoreC N) x := by
    funext x
    rw [halfDerivHN, deriv_HNcoreC]
    push_cast
    ring
  rw [h]
  exact (integrable_deriv_HNcoreC N).const_mul _

theorem deriv_HNcoreC_eq_two_halfDerivHN (N : ℕ) :
    deriv (HNcoreC N) = fun x => 2 * halfDerivHN N x := by
  funext x
  rw [deriv_HNcoreC, halfDerivHN]
  push_cast
  ring

theorem halfDerivHN_FT_eq {N : ℕ} {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∫ x : ℝ, halfDerivHN N x * echar t x) =
      (fejerTriangle t : ℂ) *
        ((Real.pi * t : ℂ) * cotC t +
          (Real.pi * Complex.I * t : ℂ) *
            (Complex.I *
              ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
                (Real.sin (Real.pi * t) : ℂ)))) := by
  have hmul := halfDeriv_FT_eq_mul
    (f := HNcoreC N) (g := halfDerivHN N)
    (integrable_HNcoreC N) (differentiable_HNcoreC N)
    (integrable_deriv_HNcoreC N)
    (deriv_HNcoreC_eq_two_halfDerivHN N) t
  rw [hmul]
  change (Real.pi * Complex.I * t : ℂ) *
      (∫ v : ℝ, (HNcore N v : ℂ) * echar t v) = _
  rw [HNcore_FT_eq_triangle_cot ht]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination
    (-(fejerTriangle t : ℂ) * (Real.pi : ℂ) * (t : ℂ) * cotC t) * hI

def gCore (M : ℕ) (x : ℝ) : ℂ :=
  (((1 / 2 : ℝ) * deriv (cesaroCore M) x : ℝ) : ℂ)

theorem gCore_eq_average (M : ℕ) (x : ℝ) :
    gCore M x =
      (1 / (M : ℝ) : ℂ) *
        ∑ N ∈ Finset.range M, halfDerivHN N x := by
  unfold gCore halfDerivHN
  rw [deriv_cesaroCore_eq]
  push_cast
  rw [Finset.mul_sum]
  calc
    (1 / 2 : ℂ) * ∑ N ∈ Finset.range M,
        (1 / (M : ℝ) : ℂ) * ((deriv (HNcore N) x : ℝ) : ℂ)
        = ∑ N ∈ Finset.range M,
            (1 / 2 : ℂ) * ((1 / (M : ℝ) : ℂ) * ((deriv (HNcore N) x : ℝ) : ℂ)) := by
              rw [Finset.mul_sum]
    _ = ∑ N ∈ Finset.range M,
          (1 / (M : ℝ) : ℂ) * ((1 / 2 : ℂ) * ((deriv (HNcore N) x : ℝ) : ℂ)) := by
          refine Finset.sum_congr rfl (fun N _ => by ring)
    _ = (1 / (M : ℝ) : ℂ) *
          ∑ N ∈ Finset.range M,
            (1 / 2 : ℂ) * ((deriv (HNcore N) x : ℝ) : ℂ) := by
          rw [Finset.mul_sum]

theorem integrable_gCore (M : ℕ) :
    Integrable (gCore M) (volume : Measure ℝ) := by
  have hfun :
      gCore M =
        fun x : ℝ =>
          (1 / (M : ℝ) : ℂ) *
            ∑ N ∈ Finset.range M, halfDerivHN N x := by
    funext x
    exact gCore_eq_average M x
  rw [hfun]
  exact (MeasureTheory.integrable_finsetSum _
    (fun N _ => integrable_halfDerivHN N)).const_mul _

theorem gCore_echar_integral (M : ℕ) (hM : 0 < M) {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∫ x : ℝ, gCore M x * echar t x) =
      (1 / (M : ℝ) : ℂ) *
        ∑ N ∈ Finset.range M,
          (fejerTriangle t : ℂ) *
            ((Real.pi * t : ℂ) * cotC t +
              (Real.pi * Complex.I * t : ℂ) *
                (Complex.I *
                  ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
                    (Real.sin (Real.pi * t) : ℂ)))) := by
  have hfun :
      (fun x : ℝ => gCore M x * echar t x) =
        fun x : ℝ =>
          (1 / (M : ℝ) : ℂ) *
            ∑ N ∈ Finset.range M, halfDerivHN N x * echar t x := by
    funext x
    rw [gCore_eq_average M x, ← Finset.sum_mul]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum]
  · refine congrArg ((1 / (M : ℝ) : ℂ) * ·) ?_
    refine Finset.sum_congr rfl (fun N _ => ?_)
    exact halfDerivHN_FT_eq ht
  · intro N _
    exact (integrable_halfDerivHN N).mul_bdd
      (by
        exact (by unfold echar; fun_prop :
          Continuous (fun x : ℝ => echar t x)).aestronglyMeasurable)
      (by
        filter_upwards with x
        unfold echar
        rw [show (-2 : ℂ) * Real.pi * Complex.I * t * x =
            ((-2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
          Complex.norm_exp_ofReal_mul_I])

theorem canonical_fejerTriangle_eq (t : ℝ) :
    VaalerCesaroRemainderL2.fejerTriangle t = fejerTriangle t := rfl

theorem cesaroSum_collapse {M : ℕ} (hM : 0 < M) {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (1 / (M : ℝ) : ℂ) *
        ∑ N ∈ Finset.range M,
          (fejerTriangle t : ℂ) *
            ((Real.pi * t : ℂ) * cotC t +
              (Real.pi * Complex.I * t : ℂ) *
                (Complex.I *
                  ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
                    (Real.sin (Real.pi * t) : ℂ)))) =
      (fejerTriangle t : ℂ) * (Real.pi * t : ℂ) * cotC t +
        (VaalerCesaroRemainderL2.Ravg M t : ℂ) := by
  have hMC : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMCc : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hMC
  have hsinC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hsplit : ∀ N ∈ Finset.range M,
      (fejerTriangle t : ℂ) *
        ((Real.pi * t : ℂ) * cotC t +
          (Real.pi * Complex.I * t : ℂ) *
            (Complex.I *
              ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
                (Real.sin (Real.pi * t) : ℂ)))) =
      (fejerTriangle t : ℂ) * ((Real.pi * t : ℂ) * cotC t) +
        (fejerTriangle t : ℂ) *
          ((-(Real.pi * t) : ℂ) *
            ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
              (Real.sin (Real.pi * t) : ℂ))) := by
    intro N _
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination
      (fejerTriangle t : ℂ) * (Real.pi : ℂ) * (t : ℂ) *
        ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
          (Real.sin (Real.pi * t) : ℂ)) * hI
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, mul_add]
  have hcancel :
      ((1 : ℂ) / (((M : ℝ) : ℂ))) * (((M : ℝ) : ℂ)) = 1 := by
    field_simp [hMCc]
  have hprinc :
      (1 / (M : ℝ) : ℂ) *
          ((M : ℕ) •
            ((fejerTriangle t : ℂ) *
              ((Real.pi * t : ℂ) * cotC t))) =
        (fejerTriangle t : ℂ) * (Real.pi * t : ℂ) * cotC t := by
    rw [nsmul_eq_mul]
    push_cast
    calc
      (1 / (((M : ℝ) : ℂ))) *
          (((M : ℝ) : ℂ) * ((fejerTriangle t : ℂ) * ((Real.pi * t : ℂ) * cotC t))) =
        (((1 : ℂ) / (((M : ℝ) : ℂ))) * (((M : ℝ) : ℂ))) *
          ((fejerTriangle t : ℂ) * ((Real.pi * t : ℂ) * cotC t)) := by ring
      _ = (fejerTriangle t : ℂ) * ((Real.pi * t : ℂ) * cotC t) := by rw [hcancel]; simp
      _ = (fejerTriangle t : ℂ) * (Real.pi * t : ℂ) * cotC t := by ring
  rw [hprinc]
  congr 1
  rw [← Finset.mul_sum]
  have hinner :
      (∑ N ∈ Finset.range M,
        (-(Real.pi * t) : ℂ) *
          ((Real.cos (Real.pi * (2 * N + 1) * t) : ℂ) /
            (Real.sin (Real.pi * t) : ℂ))) =
      (-(Real.pi * t) : ℂ) / (Real.sin (Real.pi * t) : ℂ) *
        (((∑ N ∈ Finset.range M,
          Real.cos ((2 * (N : ℝ) + 1) * (Real.pi * t))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    have hc : Real.cos (Real.pi * (2 * N + 1) * t) =
        Real.cos ((2 * (N : ℝ) + 1) * (Real.pi * t)) := by
      congr 1
      ring
    rw [hc]
    ring
  rw [hinner]
  rw [sum_cos_odd_eq ht M]
  unfold VaalerCesaroRemainderL2.Ravg
  rw [canonical_fejerTriangle_eq]
  push_cast
  field_simp [hMCc, hsinC]

def jPrincipalC (t : ℝ) : ℂ :=
  h3VaalerJHatContC t - jTailC t

theorem principal_eq_jPrincipalC {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (fejerTriangle t : ℂ) * (Real.pi * t : ℂ) * cotC t =
      jPrincipalC t := by
  unfold jPrincipalC h3VaalerJHatContC jTailC
  by_cases h1 : 1 ≤ |t|
  · rw [fejerTriangle_eq_zero_of_one_le_abs h1]
    simp [h3VaalerJHatCont, jTail, h1]
  · have hlt : |t| < 1 := not_le.mp h1
    have ht0 : t ≠ 0 := by
      intro h
      subst t
      simp at ht
    have htri : fejerTriangle t = 1 - |t| :=
      fejerTriangle_eq_one_sub_abs_of_abs_le_one (le_of_lt hlt)
    have hcotC : cotC t = ((Real.cot (Real.pi * t) : ℝ) : ℂ) := by
      unfold cotC
      rw [Real.cot_eq_cos_div_sin]
      push_cast
      rfl
    have hcot_odd : Real.cot (Real.pi * (-t)) = -Real.cot (Real.pi * t) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, mul_neg,
        Real.cos_neg, Real.sin_neg]
      ring
    have hkey : t * Real.cot (Real.pi * t) =
        |t| * Real.cot (Real.pi * |t|) := by
      rcases lt_or_gt_of_ne ht0 with hneg | hpos
      · rw [abs_of_neg hneg, hcot_odd]
        ring
      · rw [abs_of_pos hpos]
    rw [htri, hcotC]
    simp only [h3VaalerJHatCont, jTail, if_neg h1, if_neg ht0]
    rw [show (((1 - |t| : ℝ) : ℂ) *
          (((Real.pi : ℝ) : ℂ) * ((t : ℝ) : ℂ)) *
          ((Real.cot (Real.pi * t) : ℝ) : ℂ)) =
        ((Real.pi * (1 - |t|) * (t * Real.cot (Real.pi * t)) : ℝ) : ℂ) by
          push_cast
          ring]
    norm_cast
    rw [hkey]
    ring

theorem gCore_echar_integral_eq {M : ℕ} (hM : 0 < M) {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∫ x : ℝ, gCore M x * echar t x) =
      jPrincipalC t + (VaalerCesaroRemainderL2.Ravg M t : ℂ) := by
  rw [gCore_echar_integral M hM ht, cesaroSum_collapse hM ht,
    principal_eq_jPrincipalC ht]

theorem ae_sin_pi_mul_ne_zero :
    ∀ᵐ t : ℝ, Real.sin (Real.pi * t) ≠ 0 := by
  exact H3VaalerCesaroPointwise.sin_pi_ne_zero_ae

theorem fourier_gCore_ae {M : ℕ} (hM : 0 < M) :
    𝓕 (gCore M) =ᵐ[volume]
      fun t => jPrincipalC t +
        (VaalerCesaroRemainderL2.Ravg M t : ℂ) := by
  filter_upwards [ae_sin_pi_mul_ne_zero] with t ht
  rw [← integral_mul_echar_eq_fourier]
  exact gCore_echar_integral_eq hM ht

#print axioms HNcore_FT_eq_triangle_cot
#print axioms halfDerivHN_FT_eq
#print axioms gCore_echar_integral_eq
#print axioms fourier_gCore_ae

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCoreFourier
