module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer

@[expose] public section

noncomputable section

open Real Filter Topology Metric
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer

noncomputable def h3NegTailSum (x : ℝ) : ℝ :=
  ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2

theorem h3NegTail_localUnifBound {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ r : ℝ, 0 < r ∧
      (Metric.ball x₀ r ⊆ (Set.range ((↑) : ℤ → ℝ))ᶜ) ∧
      Summable (fun k : ℕ =>
        2 * ((2 : ℝ) ^ 3 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3)) ∧
      (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ r →
        ‖-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3‖ ≤
          2 * ((2 : ℝ) ^ 3 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3)) := by
  obtain ⟨r, hr, hball, hsum, hbound⟩ :=
    negShift_pow_localUnifBound hx₀ 3 (by norm_num)
  refine ⟨r, hr, hball, hsum.mul_left 2, ?_⟩
  intro k y hy
  have hb := hbound k y hy
  calc
    ‖-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3‖
        = 2 * |y - (k + 1 : ℕ)|⁻¹ ^ 3 := by
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_inv]
            norm_num
    _ ≤ 2 * ((2 : ℝ) ^ 3 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_h3NegTailSum {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3NegTailSum
      (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3) x := by
  obtain ⟨r, hrpos, hball_sub, hUsum, hUbound⟩ :=
    h3NegTail_localUnifBound hx
  set t : Set ℝ := Metric.ball x r with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htconn : IsPreconnected t := (convex_ball x r).isPreconnected
  have hxmem : x ∈ t := Metric.mem_ball_self hrpos
  have hg : ∀ (k : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z : ℝ => (z - (k + 1 : ℕ))⁻¹ ^ 2)
        (-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3) y := by
    intro k y hy
    have hyc : y ∈ (Set.range ((↑) : ℤ → ℝ))ᶜ := hball_sub hy
    have hne : y - (k + 1 : ℕ) ≠ 0 := by
      intro h
      apply hyc
      refine ⟨(k + 1 : ℕ), ?_⟩
      push_cast
      push_cast at h
      linarith
    exact hasDerivAt_invSq_shift (k + 1 : ℕ) y hne
  have hg0 : Summable (fun k : ℕ => (x - (k + 1 : ℕ))⁻¹ ^ 2) :=
    summable_invSq_shift_neg x
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ =>
      2 * ((2 : ℝ) ^ 3 * |x - (k + 1 : ℕ)|⁻¹ ^ 3))
    (g := fun (k : ℕ) (z : ℝ) => (z - (k + 1 : ℕ))⁻¹ ^ 2)
    (g' := fun (k : ℕ) (y : ℝ) => -2 * (y - (k + 1 : ℕ))⁻¹ ^ 3)
    hUsum htopen htconn hg hUbound hxmem hg0 hxmem
  have hfun : h3NegTailSum =
      fun z : ℝ => ∑' k : ℕ, (z - (k + 1 : ℕ))⁻¹ ^ 2 := by
    funext z
    rfl
  rw [hfun]
  exact hmain

theorem h3TailSum_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := by
  have h := summable_invSq_shift_neg (-x)
  refine h.congr ?_
  intro k
  have harg : ((-x) - (k + 1 : ℕ) : ℝ) =
      -(x + (k + 1 : ℕ)) := by
    push_cast
    ring
  rw [harg, inv_neg, neg_pow]
  norm_num

theorem hasDerivAt_h3PosTail_term (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2)
      (-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3) y := by
  let c : ℝ := -((k : ℝ) + 1)
  have hx : y - c ≠ 0 := by
    have hpos : (0 : ℝ) < y + ((k : ℝ) + 1) := by positivity
    dsimp [c]
    intro h
    nlinarith [hpos]
  have h := hasDerivAt_invSq_shift c y hx
  have hfun :
      (fun z : ℝ => (z - c)⁻¹ ^ 2) =
        (fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2) := by
    funext z
    dsimp [c]
    push_cast
    ring_nf
  have hval :
      (-2 * (y - c)⁻¹ ^ 3) =
        -2 * (y + (k + 1 : ℕ))⁻¹ ^ 3 := by
    dsimp [c]
    push_cast
    ring_nf
  rw [hfun, hval] at h
  exact h

theorem h3TailDerivSummable_pos {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
  apply Summable.mul_left
  have hsq := h3TailSum_summable hx
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsq
  have hb1 : (1 : ℝ) ≤ x + (k + 1 : ℕ) := by
    push_cast
    nlinarith [hx, Nat.cast_nonneg (α := ℝ) k]
  have hinv : (x + (k + 1 : ℕ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hb1
  calc
    (x + (k + 1 : ℕ))⁻¹ ^ 3
        = (x + (k + 1 : ℕ))⁻¹ ^ 2 *
          (x + (k + 1 : ℕ))⁻¹ := by ring
    _ ≤ (x + (k + 1 : ℕ))⁻¹ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (x + (k + 1 : ℕ))⁻¹ ^ 2 := by ring

theorem h3PosTail_localUnifBound {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Summable (fun k : ℕ => 2 * (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3) ∧
    (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ (x₀ / 2) →
      ‖-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3‖ ≤
        2 * (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3) := by
  have hhalf : 0 < x₀ / 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hneg := (h3TailDerivSummable_pos hhalf).neg
    refine hneg.congr ?_
    intro k
    ring
  · intro k y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hylb : x₀ / 2 < y := by
      rcases abs_lt.mp hy with ⟨h1, _⟩
      linarith
    have hbpos : (0 : ℝ) < x₀ / 2 + (k + 1 : ℕ) := by positivity
    have hle : x₀ / 2 + (k + 1 : ℕ) ≤ y + (k + 1 : ℕ) := by linarith
    have hyplus : (0 : ℝ) < y + (k + 1 : ℕ) := by
      have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
      nlinarith
    have hinv : (y + (k + 1 : ℕ))⁻¹ ≤
        (x₀ / 2 + (k + 1 : ℕ))⁻¹ := inv_anti₀ hbpos hle
    have hinvnonneg : (0 : ℝ) ≤ (y + (k + 1 : ℕ))⁻¹ :=
      (inv_pos.mpr hyplus).le
    have hpow : (y + (k + 1 : ℕ))⁻¹ ^ 3 ≤
        (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3 :=
      pow_le_pow_left₀ hinvnonneg hinv 3
    have hnn : (0 : ℝ) ≤ (y + (k + 1 : ℕ))⁻¹ ^ 3 :=
      pow_nonneg hinvnonneg _
    rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [hnn]), neg_mul]
    linarith [hpow]

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_h3TailSum {x : ℝ} (hx : 0 < x) :
    HasDerivAt h3TailSum
      (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) x := by
  obtain ⟨hUsum, hUbound⟩ := h3PosTail_localUnifBound hx
  have hhalf : 0 < x / 2 := by positivity
  set t : Set ℝ := Metric.ball x (x / 2) with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htconn : IsPreconnected t := (convex_ball x (x / 2)).isPreconnected
  have hxmem : x ∈ t := Metric.mem_ball_self hhalf
  have hg : ∀ (k : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2)
        (-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3) y := by
    intro k y hy
    rw [ht, Metric.mem_ball, Real.dist_eq] at hy
    have hypos : 0 < y := by
      rcases abs_lt.mp hy with ⟨h1, _⟩
      linarith
    exact hasDerivAt_h3PosTail_term k hypos
  have hg0 := h3TailSum_summable hx
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => 2 * (x / 2 + (k + 1 : ℕ))⁻¹ ^ 3)
    (g := fun (k : ℕ) (z : ℝ) => (z + (k + 1 : ℕ))⁻¹ ^ 2)
    (g' := fun (k : ℕ) (y : ℝ) => -2 * (y + (k + 1 : ℕ))⁻¹ ^ 3)
    hUsum htopen htconn hg hUbound hxmem hg0 hxmem
  have hfun : h3TailSum =
      fun z : ℝ => ∑' k : ℕ, (z + (k + 1 : ℕ))⁻¹ ^ 2 := by
    funext z
    rfl
  rw [hfun]
  exact hmain

theorem hasDerivAt_h3InterpBracket {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3InterpBracket
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)
          + 2 * (-(x⁻¹ ^ 2)))) x := by
  have hneg := hasDerivAt_h3NegTailSum hx
  have hpos := (hasDerivAt_h3TailSum hxpos).neg
  have hxne : x ≠ 0 := hxpos.ne'
  have hinv : HasDerivAt (fun z : ℝ => 2 * z⁻¹)
      (2 * (-(x⁻¹ ^ 2))) x := by
    have h := hasDerivAt_inv hxne
    convert h.const_mul (2 : ℝ) using 1 <;> ring
  have hsum := hneg.add (hpos.add hinv)
  have hfun : h3InterpBracket =
      fun z : ℝ => h3NegTailSum z + (-h3TailSum z + 2 * z⁻¹) := by
    funext z
    unfold h3InterpBracket h3NegTailSum
    ring
  rw [hfun]
  exact hsum

theorem h3Sin_pi_mul_ne_zero_of_notMem {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Real.sin (Real.pi * x) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro n hn
  apply hx
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hxe : (n : ℝ) * Real.pi = x * Real.pi := by
    rw [hn]
    ring
  exact mul_right_cancel₀ hpi hxe

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_h3InterpH_explicit {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3InterpH
      ((2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi)) * h3InterpBracket x
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
            + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)
              + 2 * (-(x⁻¹ ^ 2))))) x := by
  have hsin := h3Sin_pi_mul_ne_zero_of_notMem hx
  have hsinpi : HasDerivAt
      (fun z : ℝ => Real.sin (Real.pi * z))
      (Real.cos (Real.pi * x) * Real.pi) x := by
    have hinner : HasDerivAt (fun z : ℝ => Real.pi * z) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    exact (Real.hasDerivAt_sin (Real.pi * x)).comp x hinner
  have hdiv := hsinpi.div_const Real.pi
  have hsq : HasDerivAt
      (fun z : ℝ => (Real.sin (Real.pi * z) / Real.pi) ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
        (Real.cos (Real.pi * x) * Real.pi / Real.pi)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hbr := hasDerivAt_h3InterpBracket hxpos hx
  have hprod := hsq.mul hbr
  have hcont : ContinuousAt (fun z : ℝ => Real.sin (Real.pi * z)) x := by
    fun_prop
  have hnhds : ∀ᶠ z : ℝ in nhds x, Real.sin (Real.pi * z) ≠ 0 :=
    hcont.eventually_ne hsin
  have heq :
      (fun z : ℝ =>
        (Real.sin (Real.pi * z) / Real.pi) ^ 2 * h3InterpBracket z)
      =ᶠ[nhds x] h3InterpH := by
    filter_upwards [hnhds] with z hz
    unfold h3InterpH
    rw [if_neg hz]
  exact hprod.congr_of_eventuallyEq heq.symm

theorem h3Cube_eq_sq_mul (z : ℝ) :
    z⁻¹ ^ 3 = z⁻¹ ^ 2 * z⁻¹ := by
  ring

theorem h3InterpH_deriv_rhs_eq_two_G {x : ℝ} (hx : x ≠ 0) :
    ((2 * (Real.sin (Real.pi * x) / Real.pi) *
        (Real.cos (Real.pi * x) * Real.pi / Real.pi)) * h3InterpBracket x
      + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
          + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)
            + 2 * (-(x⁻¹ ^ 2)))))
      = 2 * h3G x := by
  have hneg : (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3) =
      ∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
        (x - (k + 1 : ℕ))⁻¹ := by
    refine tsum_congr ?_
    intro k
    rw [h3Cube_eq_sq_mul]
    ring
  have hpos : (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) =
      ∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
        (x + (k + 1 : ℕ))⁻¹ := by
    refine tsum_congr ?_
    intro k
    rw [h3Cube_eq_sq_mul]
    ring
  rw [hneg, hpos, h3G_eq_of_ne_zero hx]
  ring

theorem hasDerivAt_h3InterpH_two_G {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3InterpH (2 * h3G x) x := by
  have h := hasDerivAt_h3InterpH_explicit hxpos hx
  rwa [h3InterpH_deriv_rhs_eq_two_G (ne_of_gt hxpos)] at h

theorem hasDerivAt_h3InterpH_two_reJ {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt h3InterpH (2 * (h3VaalerJ x).re) x := by
  have hG : h3G x = (h3VaalerJ x).re := GEqReJ_holds x hxpos hx
  have h := hasDerivAt_h3InterpH_two_G hxpos hx
  rwa [hG] at h

#print axioms hasDerivAt_h3InterpH_two_G
#print axioms hasDerivAt_h3InterpH_two_reJ

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ
