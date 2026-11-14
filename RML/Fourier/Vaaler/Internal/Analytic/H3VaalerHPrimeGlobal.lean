module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobal

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable

theorem h3InterpBracket_neg (x : ℝ) :
    h3InterpBracket (-x) = - h3InterpBracket x := by
  have hneg :
      (∑' k : ℕ, ((-x) - (k + 1 : ℕ))⁻¹ ^ 2) =
        ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
    refine tsum_congr ?_
    intro k
    have harg : ((-x) - (k + 1 : ℕ) : ℝ) =
        -(x + (k + 1 : ℕ)) := by
      push_cast
      ring
    rw [harg, inv_neg, neg_pow]
    norm_num
  have hpos :
      (∑' k : ℕ, ((-x) + (k + 1 : ℕ))⁻¹ ^ 2) =
        ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2 := by
    refine tsum_congr ?_
    intro k
    have harg : ((-x) + (k + 1 : ℕ) : ℝ) =
        -(x - (k + 1 : ℕ)) := by
      push_cast
      ring
    rw [harg, inv_neg, neg_pow]
    norm_num
  unfold h3InterpBracket h3TailSum
  rw [hneg, hpos]
  have hinv : (-x)⁻¹ = -(x⁻¹) := by rw [inv_neg]
  rw [hinv]
  ring

theorem h3InterpH_neg (x : ℝ) :
    h3InterpH (-x) = - h3InterpH x := by
  unfold h3InterpH
  have hsin : Real.sin (Real.pi * (-x)) = - Real.sin (Real.pi * x) := by
    rw [mul_neg, Real.sin_neg]
  rw [hsin]
  by_cases hx : Real.sin (Real.pi * x) = 0
  · rw [if_pos]
    · rw [if_pos hx, Real.sign_neg]
    · simp [hx]
  · rw [if_neg]
    · rw [if_neg hx, h3InterpBracket_neg]
      ring
    · simp [hx]

theorem h3VaalerJ_even (x : ℝ) :
    h3VaalerJ (-x) = h3VaalerJ x := by
  unfold h3VaalerJ
  let A : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hcomp :
      (fun t : ℝ => RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC (-t)) =
        RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC := by
    funext t
    exact JHat_even_C t
  have h := Real.fourierInv_comp_linearIsometry A
    RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC x
  change 𝓕⁻
      (RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC ∘ A) x =
    𝓕⁻ RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC (-x) at h
  have hfun :
      (RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC ∘ A) =
        RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC := by
    funext t
    exact JHat_even_C t
  rw [hfun] at h
  exact h.symm

theorem hasDerivAt_h3InterpH_two_reJ_off_lattice
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3InterpH (2 * (h3VaalerJ x).re) x := by
  by_cases hx0 : x = 0
  · subst x
    exfalso
    apply hx
    exact ⟨0, by simp⟩
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hnegRange : -x ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨n, hn⟩
      apply hx
      refine ⟨-n, ?_⟩
      push_cast
      linarith
    have hbase :
        HasDerivAt h3InterpH (2 * (h3VaalerJ (-x)).re) (-x) :=
      hasDerivAt_h3InterpH_two_reJ (by linarith) hnegRange
    have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
      refine ((hasDerivAt_id x).neg).congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    have hreflection :
        HasDerivAt (fun y : ℝ => -h3InterpH (-y))
          (2 * (h3VaalerJ x).re) x := by
      refine (((hbase.comp x hneg).neg).congr_deriv ?_).congr_of_eventuallyEq ?_
      · rw [h3VaalerJ_even]
        ring
      · filter_upwards with y
        rfl
    refine hreflection.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [h3InterpH_neg]
    ring
  · exact hasDerivAt_h3InterpH_two_reJ hxpos hx

theorem h3Sin_pi_mul_ne_zero_of_notMem_global {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Real.sin (Real.pi * x) ≠ 0 :=
  h3Sin_pi_mul_ne_zero_of_notMem hx

#print axioms h3InterpH_neg
#print axioms h3VaalerJ_even
#print axioms hasDerivAt_h3InterpH_two_reJ_off_lattice

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobal
