module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCFourier
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Metric Set
open scoped BigOperators FourierTransform

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCFourier

theorem summable_invSq_shift_neg (x : ℝ) :
    Summable (fun k : ℕ => (x - (k + 1 : ℕ))⁻¹ ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  rw [← summable_nat_add_iff N]
  have hpser : Summable (fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    rw [← summable_nat_add_iff 1] at hp
    refine hp.congr ?_
    intro k
    push_cast
    rw [inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hpser
  have hbase_pos : (0 : ℝ) < (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN, Nat.cast_nonneg (α := ℝ) k]
  have hge : ((k : ℝ) + 1) ≤ (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN.le]
  have hcast : (x - ((k + N : ℕ) + 1 : ℕ) : ℝ) =
      -(((N : ℝ) + (k : ℝ) + 1) - x) := by
    push_cast
    ring
  rw [hcast]
  have hsimp : (-(((N : ℝ) + (k : ℝ) + 1) - x))⁻¹ ^ 2 =
      (((N : ℝ) + (k : ℝ) + 1) - x)⁻¹ ^ 2 := by
    rw [← neg_inv, neg_pow]
    simp
  rw [hsimp, inv_pow, inv_pow]
  have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsqle : ((k : ℝ) + 1) ^ 2 ≤
      (((N : ℝ) + (k : ℝ) + 1) - x) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hbase_pos, hpos1]
    · linarith
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  linarith [hsqle]

theorem summable_invCube_shift_neg (x : ℝ) :
    Summable (fun k : ℕ => |x - (k + 1 : ℕ)|⁻¹ ^ 3) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  rw [← summable_nat_add_iff N]
  have hpser : Summable (fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 3) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    rw [← summable_nat_add_iff 1] at hp
    refine hp.congr ?_
    intro k
    push_cast
    rw [inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hpser
  have hbase_pos : (0 : ℝ) < (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN, Nat.cast_nonneg (α := ℝ) k]
  have hge : ((k : ℝ) + 1) ≤ (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN.le]
  have hcast : (x - ((k + N : ℕ) + 1 : ℕ) : ℝ) =
      -(((N : ℝ) + (k : ℝ) + 1) - x) := by
    push_cast
    ring
  rw [hcast, abs_neg, abs_of_pos hbase_pos]
  have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [inv_pow, inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
  exact pow_le_pow_left₀ hpos1.le hge 3

theorem negShift_pow_localUnifBound {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ∃ r : ℝ, 0 < r ∧
      (Metric.ball x₀ r ⊆ (Set.range ((↑) : ℤ → ℝ))ᶜ) ∧
      Summable (fun k : ℕ => (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) ∧
      (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ r →
        |y - (k + 1 : ℕ)|⁻¹ ^ p ≤
          (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) := by
  classical
  set s : Set ℝ := Set.range ((↑) : ℤ → ℝ)
  have hsclosed : IsClosed s := Real.isClosed_range_intCast
  have hsne : s.Nonempty := ⟨(0 : ℝ), ⟨0, by simp⟩⟩
  set δ : ℝ := Metric.infDist x₀ s
  have hδpos : 0 < δ := by
    rw [← hsclosed.notMem_iff_infDist_pos hsne]
    exact hx₀
  set r : ℝ := δ / 2
  have hrpos : 0 < r := by positivity
  have hlb₀ : ∀ k : ℕ, δ ≤ |x₀ - (k + 1 : ℕ)| := by
    intro k
    have hmem : ((k + 1 : ℕ) : ℝ) ∈ s := ⟨(k + 1 : ℕ), by push_cast; ring⟩
    have h := Metric.infDist_le_dist_of_mem (x := x₀) hmem
    simpa [Real.dist_eq] using h
  refine ⟨r, hrpos, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball] at hz
    intro hzmem
    have h := Metric.infDist_le_dist_of_mem (x := x₀) hzmem
    rw [dist_comm] at h
    dsimp [r] at hz
    linarith
  · have hsq : Summable (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2) := by
      refine (summable_invSq_shift_neg x₀).congr ?_
      intro k
      rw [← abs_inv, sq_abs]
    have htend : Tendsto (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹) atTop (𝓝 0) := by
      have hbase : Tendsto (fun k : ℕ => |x₀ - (k + 1 : ℕ)|) atTop atTop := by
        have hlin : Tendsto (fun k : ℕ => ((k : ℝ) + 1) - x₀) atTop atTop := by
          have hc : Tendsto (fun k : ℕ => (k : ℝ) + (1 - x₀)) atTop atTop :=
            Filter.tendsto_atTop_add_const_right atTop (1 - x₀)
              (tendsto_natCast_atTop_atTop (R := ℝ))
          refine hc.congr ?_
          intro k
          ring
        refine (tendsto_abs_atTop_atTop.comp hlin).congr ?_
        intro k
        rw [Function.comp_apply]
        rw [show ((k:ℝ) + 1) - x₀ =
          -(x₀ - ((k + 1 : ℕ) : ℝ)) by push_cast; ring, abs_neg]
      exact (tendsto_inv_atTop_zero).comp hbase
    have hev : ∀ᶠ k in atTop,
        |x₀ - (k + 1 : ℕ)|⁻¹ ^ p ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2 := by
      have h1 : ∀ᶠ k in atTop, |x₀ - (k + 1 : ℕ)|⁻¹ ≤ 1 := by
        have h := htend.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
        filter_upwards [h] with k hk
        exact hk
      filter_upwards [h1] with k hk
      have hnn : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ := by positivity
      exact pow_le_pow_of_le_one hnn hk hp
    have hsummp : Summable (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) := by
      refine summable_of_isBigO_nat hsq ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [hev] with k hk
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ p),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2)]
      exact hk
    exact hsummp.mul_left _
  · intro k y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hge : |x₀ - (k + 1 : ℕ)| / 2 ≤ |y - (k + 1 : ℕ)| := by
      have htri : |x₀ - (k + 1 : ℕ)| - |y - x₀| ≤
          |y - (k + 1 : ℕ)| := by
        have h : |x₀ - (k + 1 : ℕ)| ≤
            |y - (k + 1 : ℕ)| + |y - x₀| := by
          calc
            |x₀ - (k + 1 : ℕ)| =
                |(y - (k + 1 : ℕ)) - (y - x₀)| := by ring_nf
            _ ≤ |y - (k + 1 : ℕ)| + |y - x₀| := abs_sub _ _
        linarith
      have hrle : |y - x₀| ≤ |x₀ - (k + 1 : ℕ)| / 2 := by
        have h1 := hlb₀ k
        dsimp [r] at hy
        linarith
      linarith
    have hx0n_pos : 0 < |x₀ - (k + 1 : ℕ)| :=
      lt_of_lt_of_le hδpos (hlb₀ k)
    have hinv : |y - (k + 1 : ℕ)|⁻¹ ≤
        2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by
      have hhalfpos : (0 : ℝ) < |x₀ - (k + 1 : ℕ)| / 2 := by positivity
      have h := inv_anti₀ hhalfpos hge
      calc
        |y - (k + 1 : ℕ)|⁻¹ ≤
            (|x₀ - (k + 1 : ℕ)| / 2)⁻¹ := h
        _ = 2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
    have hpow : |y - (k + 1 : ℕ)|⁻¹ ^ p ≤
        (2 * |x₀ - (k + 1 : ℕ)|⁻¹) ^ p :=
      pow_le_pow_left₀ (by positivity) hinv p
    rw [mul_pow] at hpow
    exact hpow

theorem tsumInvPow_neg_continuousAt {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ContinuousAt (fun x : ℝ =>
      ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
  obtain ⟨r, hrpos, hball_sub, hUsum, hUbound⟩ :=
    negShift_pow_localUnifBound hx₀ p hp
  set t : Set ℝ := Metric.ball x₀ r
  have hcont : ∀ k : ℕ,
      ContinuousOn (fun x : ℝ => (x - (k + 1 : ℕ))⁻¹ ^ p) t := by
    intro k
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y hy
      have hyc : y ∈ (Set.range ((↑) : ℤ → ℝ))ᶜ := hball_sub hy
      intro h
      apply hyc
      refine ⟨(k + 1 : ℕ), ?_⟩
      push_cast
      push_cast at h
      linarith
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖(x - (k + 1 : ℕ))⁻¹ ^ p‖ ≤
        (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p := by
    intro k x hx
    have hb := hUbound k x hx
    rw [Real.norm_eq_abs]
    calc
      |(x - (k + 1 : ℕ))⁻¹ ^ p| =
          |x - (k + 1 : ℕ)|⁻¹ ^ p := by
            rw [← abs_inv, ← abs_pow]
      _ ≤ (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p := hb
  have hcontOn : ContinuousOn
      (fun x : ℝ => ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ p) t :=
    continuousOn_tsum hcont hUsum hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds x₀ hrpos)

theorem tsumInvPow_pos_continuousAt {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ContinuousAt (fun x : ℝ =>
      ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
  have hnegmem : (-x₀) ∉ Set.range ((↑) : ℤ → ℝ) := by
    intro ⟨m, hm⟩
    apply hx₀
    exact ⟨-m, by push_cast; linarith⟩
  have hbase := tsumInvPow_neg_continuousAt hnegmem p hp
  have heq :
      (fun x : ℝ => ∑' k : ℕ, ((-x) - (k + 1 : ℕ))⁻¹ ^ p) =
      (fun x : ℝ => (-1 : ℝ) ^ p *
        ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ p) := by
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr ?_
    intro k
    rw [show ((-x) - (k + 1 : ℕ)) =
      -(x + (k + 1 : ℕ)) by push_cast; ring, inv_neg, neg_pow]
  have hcomp : ContinuousAt
      (fun x : ℝ => ∑' k : ℕ, ((-x) - (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
    exact hbase.comp continuousAt_neg
  rw [heq] at hcomp
  have hc : ((-1 : ℝ) ^ p) ≠ 0 := by positivity
  have hdiv := hcomp.div_const ((-1 : ℝ) ^ p)
  refine hdiv.congr ?_
  filter_upwards with x
  field_simp

theorem h3InterpBracket_continuousAt {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt h3InterpBracket x₀ := by
  have hx0ne : x₀ ≠ 0 := by
    intro h
    apply hx₀
    exact ⟨0, by simp [h]⟩
  have h1 := tsumInvPow_neg_continuousAt hx₀ 2 (by norm_num)
  have h2 := tsumInvPow_pos_continuousAt hx₀ 2 (by norm_num)
  have h3 : ContinuousAt (fun x : ℝ => 2 * x⁻¹) x₀ := by
    exact (continuousAt_inv₀ hx0ne).const_mul 2
  have hsum : ContinuousAt
      (fun x : ℝ =>
        (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) -
        (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) + 2 * x⁻¹) x₀ :=
    (h1.sub h2).add h3
  refine hsum.congr ?_
  filter_upwards with x
  rfl

theorem h3G_continuousAt_of_notMem {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt h3G x₀ := by
  have hx0ne : x₀ ≠ 0 := by
    intro h
    apply hx₀
    exact ⟨0, by simp [h]⟩
  have hsin : ContinuousAt
      (fun x : ℝ => Real.sin (Real.pi * x) / Real.pi) x₀ := by fun_prop
  have hcos : ContinuousAt
      (fun x : ℝ => Real.cos (Real.pi * x) * Real.pi / Real.pi) x₀ := by fun_prop
  have hbr := h3InterpBracket_continuousAt hx₀
  have hfirst : ContinuousAt
      (fun x : ℝ =>
        (Real.sin (Real.pi * x) / Real.pi) *
        (Real.cos (Real.pi * x) * Real.pi / Real.pi) * h3InterpBracket x) x₀ :=
    (hsin.mul hcos).mul hbr
  have hcubeNeg : ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) x₀ := by
    have h := tsumInvPow_neg_continuousAt hx₀ 3 (by norm_num)
    have heq :
        (fun x : ℝ => ∑' k : ℕ,
          -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) =
        (fun x : ℝ => (-2 : ℝ) *
          ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3) := by
      funext x
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro k
      ring
    rw [heq]
    exact h.const_mul _
  have hcubePos : ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) x₀ := by
    have h := tsumInvPow_pos_continuousAt hx₀ 3 (by norm_num)
    have heq :
        (fun x : ℝ => ∑' k : ℕ,
          -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) =
        (fun x : ℝ => (-2 : ℝ) *
          ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
      funext x
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro k
      ring
    rw [heq]
    exact h.const_mul _
  have hxsq : ContinuousAt (fun x : ℝ => 2 * (-(x⁻¹ ^ 2))) x₀ := by
    exact ((continuousAt_inv₀ hx0ne).pow 2).neg.const_mul 2
  have hsinsq : ContinuousAt
      (fun x : ℝ => (Real.sin (Real.pi * x) / Real.pi) ^ 2) x₀ :=
    hsin.pow 2
  have hinner : ContinuousAt
      (fun x : ℝ =>
        (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
          (x - (k + 1 : ℕ))⁻¹)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
          (x + (k + 1 : ℕ))⁻¹) + 2 * (-(x⁻¹ ^ 2)))) x₀ :=
    hcubeNeg.add (hcubePos.neg.add hxsq)
  have hsecond : ContinuousAt
      (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
          (x - (k + 1 : ℕ))⁻¹)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
          (x + (k + 1 : ℕ))⁻¹) + 2 * (-(x⁻¹ ^ 2))))) x₀ :=
    (hsinsq.const_mul (1 / 2 : ℝ)).mul hinner
  have htot := hfirst.add hsecond
  refine htot.congr ?_
  have hne : ∀ᶠ x : ℝ in nhds x₀, x ≠ 0 :=
    continuousAt_id.eventually_ne hx0ne
  filter_upwards [hne] with x hx
  rw [h3G_eq_of_ne_zero hx]
  rfl

theorem h3GC_continuousAt_of_notMem {x₀ : ℝ}
    (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt h3GC x₀ := by
  exact Complex.continuous_ofReal.continuousAt.comp
    (h3G_continuousAt_of_notMem hx₀)

def h3VaalerJ (x : ℝ) : ℂ :=
  𝓕⁻ RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous.h3VaalerJHatContC x

def GEqReJ : Prop :=
  ∀ x : ℝ, 0 < x → x ∉ Set.range ((↑) : ℤ → ℝ) →
    h3G x = (h3VaalerJ x).re

theorem h3VaalerJ_continuous : Continuous h3VaalerJ := by
  unfold h3VaalerJ
  rw [Real.fourierInv_eq_fourier_comp_neg]
  apply RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement.continuous_fourier_of_integrable
  exact RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDerivLp.h3VaalerJHatContC_integrable.comp_neg

theorem h3GC_eq_h3VaalerJ_offInt :
    Set.EqOn h3GC h3VaalerJ (Set.range ((↑) : ℤ → ℝ))ᶜ := by
  let U : Set ℝ := (Set.range ((↑) : ℤ → ℝ))ᶜ
  have hUopen : IsOpen U := Real.isClosed_range_intCast.isOpen_compl
  have hae : h3GC =ᵐ[volume.restrict U] h3VaalerJ := by
    exact ae_restrict_of_ae
      RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGCIntegrable.fourierInv_JHat_ae_eq_h3GC.symm
  have hGCcont : ContinuousOn h3GC U := by
    intro x hx
    exact (h3GC_continuousAt_of_notMem hx).continuousWithinAt
  have hJcont : ContinuousOn h3VaalerJ U :=
    h3VaalerJ_continuous.continuousOn
  exact Measure.eqOn_open_of_ae_eq hae hUopen hGCcont hJcont

theorem GEqReJ_holds : GEqReJ := by
  intro x hxpos hx
  have hcx := h3GC_eq_h3VaalerJ_offInt hx
  have hre := congrArg Complex.re hcx
  simpa [h3VaalerJ] using hre

#print axioms h3G_continuousAt_of_notMem
#print axioms h3GC_eq_h3VaalerJ_offInt
#print axioms GEqReJ_holds

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
