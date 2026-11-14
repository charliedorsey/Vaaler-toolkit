module

public import RML.Fourier.Vaaler.Internal.H3VaalerPeriodizationBridge
public import Mathlib.Analysis.PSeries

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare

lemma h3ScaledVaalerKernel_le_scale (J : ℕ) (x : ℝ) :
    h3ScaledVaalerKernel J x ≤ (((J + 1 : ℕ) : ℝ)) := by
  unfold h3ScaledVaalerKernel
  rw [h3VaalerK_eq_sincSqPi]
  have h := sincSqPi_le_one ((((J + 1 : ℕ) : ℝ)) * x)
  nlinarith [show (0 : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) by positivity]

lemma h3ScaledVaalerKernel_coeff_le_one (J : ℕ) (x : ℝ) :
    (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi) ^ 2 /
      (((J + 1 : ℕ) : ℝ)) ≤ 1 := by
  have hs :
      |Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x))| ≤ 1 :=
    Real.abs_sin_le_one _
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hM : (1 : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le J)
  have hrat :
      |Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi| ≤ 1 := by
    rw [abs_div, abs_of_pos hpi0]
    apply (div_le_one hpi0).2
    exact hs.trans hpi
  have hsquare :
      (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi) ^ 2 ≤ 1 := by
    rcases abs_le.mp hrat with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg
      (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) / Real.pi)]
  have hMpos : (0 : ℝ) < (((J + 1 : ℕ) : ℝ)) := by positivity
  rw [div_le_one hMpos]
  exact hsquare.trans hM

lemma h3_periodization_far_geometry
    {n : ℤ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    (((n.natAbs + 1 : ℕ) : ℝ)) ≤ 4 * |x - (n : ℝ)| := by
  by_cases hnneg : n < 0
  · have habsZ : (n.natAbs : ℤ) = -n :=
      Int.ofNat_natAbs_of_nonpos (le_of_lt hnneg)
    have hcast0 := congrArg (fun z : ℤ => (z : ℝ)) habsZ
    have hcast : ((n.natAbs : ℕ) : ℝ) = -(n : ℝ) := by
      simpa using hcast0
    rw [Nat.cast_add, Nat.cast_one, hcast]
    have hd : 0 < x - (n : ℝ) := by
      have hnR : (n : ℝ) < 0 := by exact_mod_cast hnneg
      linarith
    rw [abs_of_pos hd]
    have hnR : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    linarith
  · have hnnonneg : 0 ≤ n := le_of_not_gt hnneg
    have hn2 : 2 ≤ n := by omega
    have habsZ : (n.natAbs : ℤ) = n :=
      Int.natAbs_of_nonneg hnnonneg
    have hcast0 := congrArg (fun z : ℤ => (z : ℝ)) habsZ
    have hcast : ((n.natAbs : ℕ) : ℝ) = (n : ℝ) := by
      simpa using hcast0
    rw [Nat.cast_add, Nat.cast_one, hcast]
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hd : x - (n : ℝ) < 0 := by linarith
    rw [abs_of_neg hd]
    linarith

lemma h3ScaledVaalerError_uniform_Ioo_bound
    (J : ℕ) (n : ℤ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(h3ScaledVaalerError J (x - (n : ℝ)) : ℂ)‖ ≤
      16 * (((J + 1 : ℕ) : ℝ)) /
        (((n.natAbs + 1 : ℕ) : ℝ) ^ 2) := by
  have hM : (1 : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le J)
  have habs :=
    h3ScaledVaalerError_abs_le_kernel J (x - (n : ℝ))
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hn0 : n = 0
  · subst n
    have hk := h3ScaledVaalerKernel_le_scale J x
    simp only [Int.cast_zero, sub_zero, Int.natAbs_zero, zero_add,
      Nat.cast_one, one_pow, div_one]
    have habs0 :
        |h3ScaledVaalerError J x| ≤ h3ScaledVaalerKernel J x := by
      simpa using habs
    have h1 :
        |h3ScaledVaalerError J x| ≤ (((J + 1 : ℕ) : ℝ)) :=
      habs0.trans hk
    nlinarith [show (0 : ℝ) ≤ (((J + 1 : ℕ) : ℝ)) by positivity]
  by_cases hn1 : n = 1
  · subst n
    have hk := h3ScaledVaalerKernel_le_scale J (x - 1)
    norm_num
    have habs1 :
        |h3ScaledVaalerError J (x - 1)| ≤
          h3ScaledVaalerKernel J (x - 1) := by
      simpa using habs
    have h1 :
        |h3ScaledVaalerError J (x - 1)| ≤ (((J + 1 : ℕ) : ℝ)) :=
      habs1.trans hk
    push_cast at h1 hM ⊢
    nlinarith
  · have hxn : x ≠ (n : ℝ) := by
      intro heq
      have hnR : (n : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := heq ▸ hx
      have hnpos : 0 < n := by exact_mod_cast hnR.1
      have hnlt : n < 1 := by exact_mod_cast hnR.2
      omega
    rw [h3ScaledVaalerKernel_sub_int_eq J n hxn] at habs
    have hC := h3ScaledVaalerKernel_coeff_le_one J x
    have hdennonneg :
        0 ≤ (1 / (x - (n : ℝ)) ^ 2 : ℝ) := by positivity
    have hgeom :=
      h3_periodization_far_geometry hx.1 hx.2 hn0 hn1
    have hsquares :
        (((n.natAbs + 1 : ℕ) : ℝ)) ^ 2 ≤
          16 * |x - (n : ℝ)| ^ 2 := by
      nlinarith
    have hrec :
        1 / (x - (n : ℝ)) ^ 2 ≤
          16 / (((n.natAbs + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      rw [← sq_abs (x - (n : ℝ))]
      field_simp
      nlinarith [hsquares]
    calc
      |h3ScaledVaalerError J (x - (n : ℝ))| ≤
          (Real.sin (Real.pi * (((J + 1 : ℕ) : ℝ) * x)) /
              Real.pi) ^ 2 /
            (((J + 1 : ℕ) : ℝ)) *
              (1 / (x - (n : ℝ)) ^ 2) := habs
      _ ≤ 1 / (x - (n : ℝ)) ^ 2 :=
        mul_le_of_le_one_left hdennonneg hC
      _ ≤ 16 / (((n.natAbs + 1 : ℕ) : ℝ)) ^ 2 := hrec
      _ ≤ 16 * (((J + 1 : ℕ) : ℝ)) /
          (((n.natAbs + 1 : ℕ) : ℝ)) ^ 2 := by
        have hden :
            0 < (((n.natAbs + 1 : ℕ) : ℝ)) ^ 2 := by positivity
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith

lemma h3_periodization_envelope_summable (J : ℕ) :
    Summable fun n : ℤ =>
      16 * (((J + 1 : ℕ) : ℝ)) /
        (((n.natAbs + 1 : ℕ) : ℝ) ^ 2) := by
  have hnat :
      Summable fun n : ℕ =>
        (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have h0 :
        Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa using (summable_nat_add_iff 1).2 h0
  have hint :
      Summable fun n : ℤ =>
        (1 : ℝ) / (((n.natAbs + 1 : ℕ) : ℝ) ^ 2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> simpa using hnat
  have hm := hint.mul_left (16 * (((J + 1 : ℕ) : ℝ)))
  refine hm.congr ?_
  intro n
  ring

theorem h3ScaledVaalerPeriodizedC_continuousOn_Ioo (J : ℕ) :
    ContinuousOn (h3ScaledVaalerPeriodizedC J) (Set.Ioo (0 : ℝ) 1) := by
  unfold h3ScaledVaalerPeriodizedC
  apply continuousOn_tsum
    (u := fun n : ℤ =>
      16 * (((J + 1 : ℕ) : ℝ)) /
        (((n.natAbs + 1 : ℕ) : ℝ) ^ 2))
  · intro n x hx
    have hne : x - (n : ℝ) ≠ 0 := by
      intro hz
      have heq : x = (n : ℝ) := sub_eq_zero.mp hz
      have hnR : (n : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := heq ▸ hx
      have hnpos : 0 < n := by exact_mod_cast hnR.1
      have hnlt : n < 1 := by exact_mod_cast hnR.2
      omega
    have hmap : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
      fun_prop
    have herr : ContinuousAt (h3ScaledVaalerError J) (x - (n : ℝ)) :=
      h3ScaledVaalerError_continuousAt_of_ne J hne
    have hcomp := @ContinuousAt.comp ℝ ℝ ℝ _ _ _
      (fun y : ℝ => y - (n : ℝ)) x (h3ScaledVaalerError J)
      herr hmap
    have hr :
        ContinuousAt
          (fun y : ℝ => h3ScaledVaalerError J (y - (n : ℝ))) x := by
      simpa [Function.comp_def] using hcomp
    exact
      (Complex.continuous_ofReal.continuousAt.comp hr).continuousWithinAt
  · exact h3_periodization_envelope_summable J
  · intro n x hx
    exact h3ScaledVaalerError_uniform_Ioo_bound J n hx

#print axioms h3ScaledVaalerPeriodizedC_continuousOn_Ioo

end RML.Fourier.Vaaler.Internal
