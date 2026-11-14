module

public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodizationFinal
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed

noncomputable def h3VaalerPolyCircle (J : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
    (fun z => h3VaalerSawCoeff J n * fourier n z)

noncomputable def h3VaalerPolyReal (J : ℕ) (x : ℝ) : ℂ :=
  h3VaalerPolyCircle J (x : AddCircle (1 : ℝ))

theorem h3_fourier_integrable_one (n : ℤ) :
    Integrable (fun z : AddCircle (1 : ℝ) => fourier n z)
      AddCircle.haarAddCircle := by
  exact (fourier n).continuous.integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem h3VaalerPolyCircle_integrable (J : ℕ) :
    Integrable (h3VaalerPolyCircle J) AddCircle.haarAddCircle := by
  unfold h3VaalerPolyCircle
  apply integrable_finsetSum'
  intro n hn
  exact (h3_fourier_integrable_one n).const_mul _

theorem fourierCoeff_h3VaalerPolyCircle (J : ℕ) (k : ℤ) :
    fourierCoeff (h3VaalerPolyCircle J) k = h3VaalerSawCoeff J k := by
  let s : Finset ℤ := Finset.Icc (-(J : ℤ)) (J : ℤ)
  let f : ℤ → AddCircle (1 : ℝ) → ℂ :=
    fun n z => h3VaalerSawCoeff J n * fourier n z
  have hf : ∀ n ∈ s, Integrable (f n) AddCircle.haarAddCircle := by
    intro n hn
    exact (h3_fourier_integrable_one n).const_mul _
  have hs := fourierCoeff.sum s f hf
  have hsk := congrFun hs k
  change fourierCoeff (h3VaalerPolyCircle J) k = _ at hsk
  have hsk' :
      fourierCoeff (h3VaalerPolyCircle J) k =
        ∑ n ∈ s, fourierCoeff (f n) k := by
    simpa only [Finset.sum_apply] using hsk
  have hterm : ∀ n : ℤ,
      fourierCoeff
        (fun z : AddCircle (1 : ℝ) => h3VaalerSawCoeff J n * fourier n z) k =
      h3VaalerSawCoeff J n * ((Pi.single n (1 : ℂ) : ℤ → ℂ) k) := by
    intro n
    rw [fourierCoeff.const_mul]
    rw [@fourierCoeff_fourier (1 : ℝ) ⟨by norm_num⟩ n]
  have hsum :
      (∑ n ∈ s, fourierCoeff (f n) k) =
      ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        h3VaalerSawCoeff J n * ((Pi.single n (1 : ℂ) : ℤ → ℂ) k) := by
    dsimp [s, f]
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n
  rw [hsk', hsum]
  by_cases hkband : k ∈ Finset.Icc (-(J : ℤ)) (J : ℤ)
  · simp [Pi.single_apply, hkband]
  · have habs : J < k.natAbs := by
      simp only [Finset.mem_Icc, not_and_or] at hkband
      rcases hkband with hlt | hlt
      · have hklt : k < -(J : ℤ) := by omega
        have hkneg : k < 0 := by omega
        have habsZ : (k.natAbs : ℤ) = -k := by
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
          omega
        exact_mod_cast (show (J : ℤ) < (k.natAbs : ℤ) by omega)
      · have hkgt : (J : ℤ) < k := by omega
        have hkpos : 0 ≤ k := by omega
        have habsZ : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hkpos
        exact_mod_cast (show (J : ℤ) < (k.natAbs : ℤ) by omega)
    rw [h3VaalerSawCoeff_eq_zero_of_band_lt habs]
    simp [Pi.single_apply, hkband]

theorem fourierCoeffOn_h3VaalerPolyReal (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (h3VaalerPolyReal J) k = h3VaalerSawCoeff J k := by
  have hc := fourierCoeff_h3VaalerPolyCircle J k
  rw [fourierCoeff_eq_intervalIntegral
    (f := h3VaalerPolyCircle J) k 0] at hc
  rw [fourierCoeffOn_eq_integral]
  simpa [h3VaalerPolyReal] using hc

def h3CenteredLinearR (x : ℝ) : ℝ := x - 1/2
def h3CenteredLinearC (x : ℝ) : ℂ := (h3CenteredLinearR x : ℂ)
def h3CenteredLinearCoeff (k : ℤ) : ℂ :=
  if k = 0 then 0 else (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))⁻¹

theorem h3Echar_int_one (k : ℤ) : h3Echar (k : ℝ) 1 = 1 := by
  unfold h3Echar
  rw [Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  push_cast
  ring

@[simp] theorem h3Echar_int_zero (k : ℤ) : h3Echar (k : ℝ) 0 = 1 := by
  simp [h3Echar]

theorem intervalIntegral_h3Echar_int_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ x : ℝ in 0..1, h3Echar (k : ℝ) x) = 0 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => h3EcharAntideriv (k : ℝ) y)
        (h3Echar (k : ℝ) x) x :=
    fun x hx => hasDerivAt_h3EcharAntideriv (by exact_mod_cast hk) x
  have hint : IntervalIntegrable (fun x : ℝ => h3Echar (k : ℝ) x) volume 0 1 :=
    (continuous_h3Echar (k : ℝ)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [h3EcharAntideriv, h3Echar_int_one] using h

theorem h3CenteredLinearC_integral_zero :
    (∫ x : ℝ in 0..1, h3CenteredLinearC x) = 0 := by
  let F : ℝ → ℝ := fun x => x^2/2 - x/2
  have hderivR : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (h3CenteredLinearR x) x := by
    intro x hx
    change HasDerivAt F (x - 1/2) x
    have h := (((hasDerivAt_id x).pow 2).div_const 2).sub
      ((hasDerivAt_id x).div_const 2)
    change HasDerivAt (fun y : ℝ => y^2 / 2 - y / 2)
      ((2:ℝ) * x^(2-1) * 1 / 2 - 1/2) x at h
    convert h using 1 <;> norm_num
  have hderivC : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => (F y : ℂ)) (h3CenteredLinearC x) x := by
    intro x hx
    simpa [h3CenteredLinearC] using (hderivR x hx).ofReal_comp
  have hint : IntervalIntegrable h3CenteredLinearC volume 0 1 := by
    exact (by unfold h3CenteredLinearC h3CenteredLinearR; fun_prop :
      Continuous h3CenteredLinearC).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivC hint
  norm_num [F] at h
  exact h

theorem fourierCoeffOn_h3CenteredLinearC (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) h3CenteredLinearC k =
      h3CenteredLinearCoeff k := by
  by_cases hk : k = 0
  · subst k
    rw [h3CenteredLinearCoeff, if_pos rfl, fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, neg_zero, fourier_zero, one_smul]
    exact h3CenteredLinearC_integral_zero
  · rw [h3CenteredLinearCoeff, if_neg hk, fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, one_smul]
    have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (u := h3CenteredLinearR) (u' := fun _ : ℝ => (1 : ℝ))
      (v := fun x : ℝ => h3EcharAntideriv (k : ℝ) x)
      (v' := fun x : ℝ => h3Echar (k : ℝ) x)
      (by
        intro x hx
        unfold h3CenteredLinearR
        simpa using (hasDerivAt_id x).sub_const (1/2 : ℝ))
      (by intro x hx; exact hasDerivAt_h3EcharAntideriv (by exact_mod_cast hk) x)
      ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable 0 1)
      ((continuous_h3Echar (k : ℝ)).intervalIntegrable 0 1)
    have hphase1 : ∀ x : ℝ,
        fourier (T := (1 : ℝ)) (-k)
          (x : AddCircle (1 : ℝ)) = h3Echar (k : ℝ) x := by
      intro x
      rw [h3_fourier_unit_eq_phase]
      unfold h3FourierPhase h3Echar
      congr 1
      push_cast
      ring
    have hphase : ∀ x : ℝ,
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) = h3Echar (k : ℝ) x := by
      intro x
      convert hphase1 x using 1 <;> norm_num
    have hres :
        (∫ x : ℝ in 0..1, (1 : ℝ) • h3EcharAntideriv (k : ℝ) x) = 0 := by
      simp only [one_smul]
      unfold h3EcharAntideriv
      rw [intervalIntegral.integral_div]
      rw [intervalIntegral_h3Echar_int_eq_zero hk]
      simp
    have hint_eq :
        (fun x : ℝ =>
          fourier (T := ((1 : ℝ) - 0)) (-k)
            (x : AddCircle ((1 : ℝ) - 0)) • h3CenteredLinearC x) =
        (fun x : ℝ => h3CenteredLinearR x • h3Echar (k : ℝ) x) := by
      funext x
      rw [hphase]
      simp [h3CenteredLinearC, Complex.real_smul, mul_comm]
    calc
      (∫ x : ℝ in 0..1,
          fourier (T := ((1 : ℝ) - 0)) (-k)
            (x : AddCircle ((1 : ℝ) - 0)) • h3CenteredLinearC x)
          = ∫ x : ℝ in 0..1, h3CenteredLinearR x • h3Echar (k : ℝ) x := by
              apply intervalIntegral.integral_congr
              intro x hx
              simpa only using congrFun hint_eq x
      _ = h3CenteredLinearR 1 • h3EcharAntideriv (k : ℝ) 1 -
          h3CenteredLinearR 0 • h3EcharAntideriv (k : ℝ) 0 := by
              rw [hibp, hres, sub_zero]
      _ = (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))⁻¹ := by
              simp [h3CenteredLinearR, h3EcharAntideriv, h3Echar_int_one]
              have hden :
                  (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 :=
                h3_neg_two_pi_I_t_ne_zero (by exact_mod_cast hk)
              field_simp [hden]
              ring


theorem h3VaalerPolyCircle_continuous (J : ℕ) :
    Continuous (h3VaalerPolyCircle J) := by
  let s : Finset ℤ := Finset.Icc (-(J : ℤ)) (J : ℤ)
  let f : ℤ → AddCircle (1 : ℝ) → ℂ :=
    fun n z => h3VaalerSawCoeff J n * fourier n z
  have h : Continuous (fun z : AddCircle (1 : ℝ) => ∑ n ∈ s, f n z) := by
    apply continuous_finset_sum
    intro n hn
    exact continuous_const.mul (map_continuous (fourier n))
  change Continuous (∑ n ∈ s, f n)
  have heq :
      (∑ n ∈ s, f n) = (fun z => ∑ n ∈ s, f n z) := by
    funext z
    simp only [Finset.sum_apply]
  rw [heq]
  exact h

theorem h3VaalerPolyReal_continuous (J : ℕ) :
    Continuous (h3VaalerPolyReal J) := by
  unfold h3VaalerPolyReal
  exact (h3VaalerPolyCircle_continuous J).comp (AddCircle.continuous_mk' _)

theorem h3CenteredLinearC_continuous :
    Continuous h3CenteredLinearC := by
  unfold h3CenteredLinearC h3CenteredLinearR
  fun_prop

noncomputable def h3PeriodizationTargetC (J : ℕ) (x : ℝ) : ℂ :=
  (2 * (((J + 1 : ℕ) : ℝ)) : ℂ) *
    (h3VaalerPolyReal J x - h3CenteredLinearC x)

theorem fourierCoeffOn_sub_h3VaalerPoly_centered
    (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun x => h3VaalerPolyReal J x - h3CenteredLinearC x) k =
      h3VaalerSawCoeff J k - h3CenteredLinearCoeff k := by
  rw [← fourierCoeffOn_h3VaalerPolyReal J k,
    ← fourierCoeffOn_h3CenteredLinearC k]
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div_one, one_smul]
  have hphase : Continuous (fun x : ℝ =>
      fourier (T := ((1 : ℝ) - 0)) (-k)
        (x : AddCircle ((1 : ℝ) - 0))) :=
    (map_continuous (fourier (-k))).comp (AddCircle.continuous_mk' _)
  have hp : IntervalIntegrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • h3VaalerPolyReal J x)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    change Continuous
      ((fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0))) * h3VaalerPolyReal J)
    exact hphase.mul (h3VaalerPolyReal_continuous J)
  have hc : IntervalIntegrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • h3CenteredLinearC x)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    change Continuous
      ((fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0))) * h3CenteredLinearC)
    exact hphase.mul h3CenteredLinearC_continuous
  have hpoint :
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) •
            (h3VaalerPolyReal J x - h3CenteredLinearC x)) =
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • h3VaalerPolyReal J x -
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • h3CenteredLinearC x) := by
    funext x
    rw [smul_sub]
  rw [hpoint, intervalIntegral.integral_sub hp hc]

theorem fourierCoeffOn_h3PeriodizationTargetC
    (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (h3PeriodizationTargetC J) k =
      if k = 0 then 0 else
        (((J + 1 : ℕ) : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I * (k : ℂ)) *
          (1 - (h3VaalerJHat J k : ℂ)) := by
  unfold h3PeriodizationTargetC
  rw [fourierCoeffOn.const_mul]
  rw [fourierCoeffOn_sub_h3VaalerPoly_centered]
  by_cases hk : k = 0
  · subst k
    simp [h3VaalerSawCoeff, h3CenteredLinearCoeff]
  · rw [if_neg hk]
    unfold h3VaalerSawCoeff h3CenteredLinearCoeff
    rw [if_neg hk, if_neg hk]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hkC, hpi, Complex.I_ne_zero]
    ring

theorem h3VaalerPolyReal_norm_le (J : ℕ) (x : ℝ) :
    ‖h3VaalerPolyReal J x‖ ≤
      ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), ‖h3VaalerSawCoeff J n‖ := by
  unfold h3VaalerPolyReal h3VaalerPolyCircle
  rw [show
      (∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        (fun z : AddCircle (1 : ℝ) =>
          h3VaalerSawCoeff J n * fourier n z)) (x : AddCircle (1 : ℝ)) =
      ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        h3VaalerSawCoeff J n * fourier n (x : AddCircle (1 : ℝ)) by
    simp only [Finset.sum_apply]]
  calc
    ‖∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        h3VaalerSawCoeff J n * fourier n (x : AddCircle (1 : ℝ))‖
      ≤ ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          ‖h3VaalerSawCoeff J n *
            fourier n (x : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          ‖h3VaalerSawCoeff J n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

theorem h3CenteredLinearC_norm_le_one_Ioc {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ‖h3CenteredLinearC x‖ ≤ 1 := by
  unfold h3CenteredLinearC h3CenteredLinearR
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem h3PeriodizationTargetC_continuous (J : ℕ) :
    Continuous (h3PeriodizationTargetC J) := by
  unfold h3PeriodizationTargetC
  exact continuous_const.mul
    ((h3VaalerPolyReal_continuous J).sub h3CenteredLinearC_continuous)

theorem h3PeriodizationTargetC_norm_le_Ioc
    (J : ℕ) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ‖h3PeriodizationTargetC J x‖ ≤
      2 * (((J + 1 : ℕ) : ℝ)) *
        ((∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          ‖h3VaalerSawCoeff J n‖) + 1) := by
  unfold h3PeriodizationTargetC
  rw [norm_mul]
  have hM : ‖(2 * (((J + 1 : ℕ) : ℝ)) : ℂ)‖ =
      2 * (((J + 1 : ℕ) : ℝ)) := by
    have hcast :
        (2 * (((J + 1 : ℕ) : ℝ)) : ℂ) =
          (((2 * (((J + 1 : ℕ) : ℝ)) : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [hM]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖h3VaalerPolyReal J x - h3CenteredLinearC x‖
        ≤ ‖h3VaalerPolyReal J x‖ + ‖h3CenteredLinearC x‖ := norm_sub_le _ _
    _ ≤ (∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          ‖h3VaalerSawCoeff J n‖) + 1 := by
      gcongr
      · exact h3VaalerPolyReal_norm_le J x
      · exact h3CenteredLinearC_norm_le_one_Ioc hx

theorem h3PeriodizationTargetC_memLp_two_Ioc (J : ℕ) :
    MemLp (h3PeriodizationTargetC J) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply MeasureTheory.MemLp.of_bound
    ((h3PeriodizationTargetC_continuous J).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self)
    (2 * (((J + 1 : ℕ) : ℝ)) *
      ((∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        ‖h3VaalerSawCoeff J n‖) + 1))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact h3PeriodizationTargetC_norm_le_Ioc J hx

theorem fourierCoeffOn_sub_of_memLp_two
    (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => f x - g x) k =
      fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f k -
      fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) g k := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div_one, one_smul]
  have hphase : Continuous (fun x : ℝ =>
      fourier (T := ((1 : ℝ) - 0)) (-k)
        (x : AddCircle ((1 : ℝ) - 0))) :=
    (map_continuous (fourier (-k))).comp (AddCircle.continuous_mk' _)
  have hf1 : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hf.integrable (by norm_num)
  have hg1 : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hg.integrable (by norm_num)
  have hfPhase : Integrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • f x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    change Integrable
      ((fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0))) • f)
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    apply hf1.bdd_smul 1
    · exact hphase.aestronglyMeasurable
    · filter_upwards with x
      rw [fourier_apply, Circle.norm_coe]
  have hgPhase : Integrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • g x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    change Integrable
      ((fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0))) • g)
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    apply hg1.bdd_smul 1
    · exact hphase.aestronglyMeasurable
    · filter_upwards with x
      rw [fourier_apply, Circle.norm_coe]
  have hfII : IntervalIntegrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • f x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hfPhase
  have hgII : IntervalIntegrable
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • g x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hgPhase
  have hpoint :
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • (f x - g x)) =
      (fun x : ℝ =>
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • f x -
        fourier (T := ((1 : ℝ) - 0)) (-k)
          (x : AddCircle ((1 : ℝ) - 0)) • g x) := by
    funext x
    rw [smul_sub]
  rw [hpoint, intervalIntegral.integral_sub hfII hgII]

theorem fourierCoeffOn_h3ScaledVaalerPeriodizedC_unconditional
    (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (h3ScaledVaalerPeriodizedC J) k =
      if k = 0 then 0 else
        (((J + 1 : ℕ) : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I * (k : ℂ)) *
          (1 - (h3VaalerJHat J k : ℂ)) := by
  rw [h3ScaledVaalerPeriodizedC_fourierCoeffOn]
  exact fourier_h3ScaledVaalerError_int
    RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCor7Closed.h3VaalerCor7TransformSpec_holds J k

noncomputable def h3PeriodizationDiffC (J : ℕ) (x : ℝ) : ℂ :=
  h3ScaledVaalerPeriodizedC J x - h3PeriodizationTargetC J x

theorem h3PeriodizationDiffC_memLp_two_Ioc (J : ℕ) :
    MemLp (h3PeriodizationDiffC J) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  unfold h3PeriodizationDiffC
  exact (h3ScaledVaalerPeriodizedC_memLp_two_Ioc J).sub
    (h3PeriodizationTargetC_memLp_two_Ioc J)

theorem fourierCoeffOn_h3PeriodizationDiffC_zero
    (J : ℕ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (h3PeriodizationDiffC J) k = 0 := by
  unfold h3PeriodizationDiffC
  rw [fourierCoeffOn_sub_of_memLp_two
    (h3ScaledVaalerPeriodizedC J) (h3PeriodizationTargetC J)
    (h3ScaledVaalerPeriodizedC_memLp_two_Ioc J)
    (h3PeriodizationTargetC_memLp_two_Ioc J) k]
  rw [fourierCoeffOn_h3ScaledVaalerPeriodizedC_unconditional,
    fourierCoeffOn_h3PeriodizationTargetC]
  ring

theorem h3PeriodizationDiffC_sq_integral_zero (J : ℕ) :
    (∫ x : ℝ in 0..1, ‖h3PeriodizationDiffC J x‖ ^ 2) = 0 := by
  have hp := tsum_sq_fourierCoeffOn
    (show (0 : ℝ) < 1 by norm_num)
    (h3PeriodizationDiffC_memLp_two_Ioc J)
  have hz :
      (∑' k : ℤ,
        ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
          (h3PeriodizationDiffC J) k‖ ^ 2) = 0 := by
    simp [fourierCoeffOn_h3PeriodizationDiffC_zero]
  rw [hz] at hp
  norm_num at hp ⊢
  exact hp.symm

theorem h3PeriodizationDiffC_ae_eq_zero_Ioc (J : ℕ) :
    h3PeriodizationDiffC J =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
  have hInt : Integrable
      (fun x : ℝ => ‖h3PeriodizationDiffC J x‖ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (h3PeriodizationDiffC_memLp_two_Ioc J).integrable_norm_pow'
  have hzero :
      (∫ x : ℝ, ‖h3PeriodizationDiffC J x‖ ^ 2
        ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := by
    have h := h3PeriodizationDiffC_sq_integral_zero J
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at h
    exact h
  have hsq :
      (fun x : ℝ => ‖h3PeriodizationDiffC J x‖ ^ 2) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg ‖h3PeriodizationDiffC J x‖) hInt).mp hzero
  filter_upwards [hsq] with x hx
  have hx0 : ‖h3PeriodizationDiffC J x‖ ^ 2 = 0 := by
    simpa using hx
  have hn : ‖h3PeriodizationDiffC J x‖ = 0 := by
    nlinarith [norm_nonneg (h3PeriodizationDiffC J x)]
  exact norm_eq_zero.mp hn

theorem h3ScaledVaalerPeriodizedC_ae_eq_target_Ioc (J : ℕ) :
    h3ScaledVaalerPeriodizedC J =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      h3PeriodizationTargetC J := by
  filter_upwards [h3PeriodizationDiffC_ae_eq_zero_Ioc J] with x hx
  unfold h3PeriodizationDiffC at hx
  exact sub_eq_zero.mp hx

theorem h3ScaledVaalerPeriodizedC_eq_target_Ioo (J : ℕ) :
    Set.EqOn (h3ScaledVaalerPeriodizedC J) (h3PeriodizationTargetC J)
      (Set.Ioo (0 : ℝ) 1) := by
  have hμ :
      volume.restrict (Set.Ioo (0 : ℝ) 1) ≤
        volume.restrict (Set.Ioc (0 : ℝ) 1) := by
    exact Measure.restrict_mono
      (by intro x hx; exact ⟨hx.1, hx.2.le⟩) (le_refl volume)
  have hae :
      h3ScaledVaalerPeriodizedC J =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        h3PeriodizationTargetC J :=
    (h3ScaledVaalerPeriodizedC_ae_eq_target_Ioc J).filter_mono
      (MeasureTheory.ae_mono hμ)
  exact Measure.eqOn_Ioo_of_ae_eq volume hae
    (h3ScaledVaalerPeriodizedC_continuousOn_Ioo J)
    (h3PeriodizationTargetC_continuous J).continuousOn

lemma h3_sum_Icc_symm {M : Type*} [AddCommMonoid M] (H : ℕ) (φ : ℤ → M) :
    ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), φ h
      = φ 0 + ∑ i ∈ Finset.range H, (φ ((i : ℤ) + 1) + φ (-((i : ℤ) + 1))) := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hset : Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
          = insert ((H : ℤ) + 1) (insert (-((H : ℤ) + 1))
              (Finset.Icc (-(H : ℤ)) (H : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnm1 : -((H : ℤ) + 1) ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      have hnm2 : ((H : ℤ) + 1) ∉
          insert (-((H : ℤ) + 1)) (Finset.Icc (-(H : ℤ)) (H : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hcast : (-(((H + 1 : ℕ)) : ℤ)) = -((H : ℤ) + 1) := by
        push_cast
        ring
      have hcast2 : (((H + 1 : ℕ)) : ℤ) = (H : ℤ) + 1 := by
        push_cast
        ring
      rw [hcast, hcast2, hset, Finset.sum_insert hnm2, Finset.sum_insert hnm1,
        ih, Finset.sum_range_succ]
      abel

theorem h3VaalerSawCoeff_pair (J : ℕ) {n : ℤ} (hn : 0 < n) (x : ℝ) :
    h3VaalerSawCoeff J n * fourier n (x : AddCircle (1 : ℝ)) +
      h3VaalerSawCoeff J (-n) * fourier (-n) (x : AddCircle (1 : ℝ))
      =
    (((-(h3VaalerJHat J n / (Real.pi * (n : ℝ))) *
      Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ)) : ℂ) := by
  have hn0 : n ≠ 0 := by omega
  have hneg0 : -n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold h3VaalerSawCoeff
  rw [if_neg hn0, if_neg hneg0, h3VaalerJHat_neg]
  rw [fourier_coe_apply, fourier_coe_apply]
  have htheta :
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / (((1 : ℝ) : ℂ))) =
      (((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have htheta_neg :
      (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / (((1 : ℝ) : ℂ))) =
      -((((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [htheta, htheta_neg]
  rw [Complex.exp_ofReal_mul_I]
  have hnegexp :
      Complex.exp (-(((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) =
        ((Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) -
          ((Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    rw [show -(((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I) =
        (((-(2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hnegexp]
  push_cast
  field_simp [hnC, hpi, Complex.I_ne_zero]
  ring

theorem h3VaalerPolyReal_eq_range (J : ℕ) (x : ℝ) :
    h3VaalerPolyReal J x =
      ∑ i ∈ Finset.range J,
        (((-(h3VaalerJHat J (((i : ℤ) + 1)) /
            (Real.pi * (((i : ℤ) + 1 : ℤ) : ℝ))) *
          Real.sin (2 * Real.pi * ((((i : ℤ) + 1 : ℤ) : ℝ)) * x) : ℝ)) : ℂ) := by
  unfold h3VaalerPolyReal h3VaalerPolyCircle
  rw [show
      (∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        (fun z : AddCircle (1 : ℝ) => h3VaalerSawCoeff J n * fourier n z))
          (x : AddCircle (1 : ℝ)) =
      ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        h3VaalerSawCoeff J n * fourier n (x : AddCircle (1 : ℝ)) by
    simp only [Finset.sum_apply]]
  rw [h3_sum_Icc_symm J
    (fun n => h3VaalerSawCoeff J n * fourier n (x : AddCircle (1 : ℝ)))]
  simp only [h3VaalerSawCoeff_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  exact h3VaalerSawCoeff_pair J (n := (i : ℤ) + 1) (by omega) x

theorem h3_range_eq_Icc (J : ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range J, f (i + 1)) =
      ∑ j ∈ Finset.Icc 1 J, f j := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show Finset.Icc 1 (J + 1) =
          insert (J + 1) (Finset.Icc 1 J) by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega]
      rw [Finset.sum_insert]
      · ac_rfl
      · simp [Finset.mem_Icc]

theorem h3VaalerPolyReal_eq_sineSum (J : ℕ) (x : ℝ) :
    h3VaalerPolyReal J x =
      ((- ∑ j ∈ Finset.Icc 1 J,
          (h3VaalerJHat J (j : ℤ) /
            (Real.pi * (j : ℝ))) *
          Real.sin (2 * Real.pi * (j : ℝ) * x) : ℝ) : ℂ) := by
  rw [h3VaalerPolyReal_eq_range]
  rw [show
      (∑ i ∈ Finset.range J,
        (((-(h3VaalerJHat J (((i : ℤ) + 1)) /
            (Real.pi * (((i : ℤ) + 1 : ℤ) : ℝ))) *
          Real.sin (2 * Real.pi * ((((i : ℤ) + 1 : ℤ) : ℝ)) * x) : ℝ)) : ℂ)) =
      ∑ i ∈ Finset.range J,
        (((-(h3VaalerJHat J ((i + 1 : ℕ) : ℤ) /
            (Real.pi * ((i + 1 : ℕ) : ℝ))) *
          Real.sin (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * x) : ℝ)) : ℂ) by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      rfl]
  have hr := h3_range_eq_Icc J
    (fun j : ℕ => (((-(h3VaalerJHat J (j : ℤ) /
      (Real.pi * (j : ℝ))) * Real.sin (2 * Real.pi * (j : ℝ) * x) : ℝ)) : ℂ))
  rw [hr]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring


theorem h3_stdAddChar_mul_im_eq_sin
    {N : ℕ} [NeZero N] (y : ZMod N) (j : ℕ) :
    (ZMod.stdAddChar ((j : ZMod N) * y)).im =
      Real.sin (2 * Real.pi * (j : ℝ) * (y.val : ℝ) / (N : ℝ)) := by
  have hpow :
      ZMod.stdAddChar ((j : ZMod N) * y) =
        (ZMod.stdAddChar y) ^ j := by
    simpa [nsmul_eq_mul, mul_comm] using
      (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := N)) j y)
  rw [hpow, h3_stdAddChar_eq_exp_val]
  rw [← Complex.exp_nat_mul]
  have harg :
      ((j : ℂ) *
          (Complex.I * ((2 * Real.pi * (y.val : ℝ) / (N : ℝ) : ℝ) : ℂ))) =
        (((2 * Real.pi * (j : ℝ) * (y.val : ℝ) / (N : ℝ) : ℝ) : ℂ) *
          Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_ofReal_mul_I_im _

theorem h3VaalerPolyReal_grid_eq_approx
    (N J : ℕ) [NeZero N] (y : ZMod N) :
    h3VaalerPolyReal J ((y.val : ℝ) / (N : ℝ)) =
      (h3VaalerApprox N J y : ℂ) := by
  rw [h3VaalerPolyReal_eq_sineSum]
  unfold h3VaalerApprox
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h3_stdAddChar_mul_im_eq_sin, Complex.ofReal_sin]
  have hargC :
      (2 : ℂ) * (Real.pi : ℂ) * (j : ℂ) *
          ((y.val : ℂ) / (N : ℂ)) =
        (((2 * Real.pi * (j : ℝ) * (y.val : ℝ) / (N : ℝ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hargC]

theorem h3CenteredLinearC_grid_eq_centeredSawtooth
    (N : ℕ) [NeZero N] {y : ZMod N} (hy : y ≠ 0) :
    h3CenteredLinearC ((y.val : ℝ) / (N : ℝ)) =
      (h3CenteredSawtooth N y : ℂ) := by
  rw [h3CenteredSawtooth_of_ne_zero hy]
  unfold h3CenteredLinearC h3CenteredLinearR
  push_cast
  rfl

theorem h3ScaledVaalerPeriodizationIdentity_holds
    (N J : ℕ) [NeZero N] :
    H3ScaledVaalerPeriodizationIdentity N J := by
  intro y hy
  let x : ℝ := (y.val : ℝ) / (N : ℝ)
  have hval0 : y.val ≠ 0 := by
    intro h0
    apply hy
    apply ZMod.val_injective
    simp [h0]
  have hval_pos : 0 < y.val := Nat.pos_of_ne_zero hval0
  have hval_lt : y.val < N := ZMod.val_lt y
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos (by exact_mod_cast hval_pos) hNpos
  have hxlt : x < 1 := by
    dsimp [x]
    rw [div_lt_one hNpos]
    exact_mod_cast hval_lt
  have hEqC := h3ScaledVaalerPeriodizedC_eq_target_Ioo J ⟨hxpos, hxlt⟩
  rw [h3ScaledVaalerPeriodizedC_eq_ofReal] at hEqC
  unfold h3PeriodizationTargetC at hEqC
  dsimp [x] at hEqC
  rw [h3VaalerPolyReal_grid_eq_approx N J y, h3CenteredLinearC_grid_eq_centeredSawtooth N hy] at hEqC
  have hcast :
      (((2 * (((J + 1 : ℕ) : ℝ))) *
        (h3VaalerApprox N J y - h3CenteredSawtooth N y) : ℝ) : ℂ) =
      ((∑' n : ℤ,
        h3ScaledVaalerError J
          ((y.val : ℝ) / (N : ℝ) - (n : ℝ))) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using hEqC.symm
  exact_mod_cast hcast


#print axioms h3ScaledVaalerPeriodizationIdentity_holds

theorem h3VaalerGridErrorSpec_holds
    (N J : ℕ) [NeZero N] :
    H3VaalerGridErrorSpec N J :=
  h3VaalerGridErrorSpec_of_scaled_periodization N J
    (h3ScaledVaalerPeriodizationIdentity_holds N J)

#print axioms h3VaalerGridErrorSpec_holds

#print axioms h3VaalerPolyReal_eq_sineSum

#print axioms fourierCoeffOn_h3VaalerPolyReal
#print axioms fourierCoeffOn_h3CenteredLinearC
#print axioms fourierCoeffOn_h3PeriodizationTargetC
#print axioms h3PeriodizationTargetC_memLp_two_Ioc
#print axioms h3PeriodizationDiffC_sq_integral_zero
#print axioms h3ScaledVaalerPeriodizedC_eq_target_Ioo

end RML.Fourier.Vaaler.Internal
