module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobal
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

noncomputable section

open Real Filter Topology Metric
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerInterpHContinuous

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerGEqReJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeEqTwoJ
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerHPrimeGlobal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerShiftedFejer
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare
open RML.Fourier.Vaaler.Internal

theorem summable_invSq_shift_pos (x : ℝ) :
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

theorem ball_half_int_eq {n : ℤ} {y : ℝ} (hy : y ∈ Metric.ball (n : ℝ) (1 / 2))
    {m : ℤ} (hm : (m : ℝ) = y) : m = n := by
  rw [Metric.mem_ball, Real.dist_eq] at hy
  rw [← hm] at hy
  -- |m - n| < 1/2 with m,n integers ⇒ m = n
  by_contra hne
  have : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hne)
    calc (1 : ℝ) ≤ (|m - n| : ℤ) := by exact_mod_cast h1
      _ = |((m - n : ℤ) : ℝ)| := by rw [Int.cast_abs]
      _ = |(m : ℝ) - (n : ℝ)| := by push_cast; rfl
  linarith

/-! ## §2 — Punctured negative tail: continuity at `n` of the term-removed `^2` series -/

/-- **PROVEN.**  For an integer `n`, the negative `^2`-tail with the singular term
`k = n−1` removed (set to `0` via `ite`) is continuous at `x = n`.

On `ball n (1/2)`: the removed term is continuously `0`; for the kept terms
`k ≠ n−1` the pole `k+1 ≠ n`, so `|n−(k+1)| ≥ 1` and the term is continuous on the
ball, dominated by the summable envelope `4·|n−(k+1)|⁻²`. -/
theorem puncturedNegTail_continuousAt (n : ℤ) :
    ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2)) (n : ℝ) := by
  classical
  set t : Set ℝ := Metric.ball (n : ℝ) (1 / 2) with ht
  -- envelope is summable: 4·|n−(k+1)|⁻²
  have hEnv : Summable (fun k : ℕ => (4 : ℝ) * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 2) := by
    have h := summable_invSq_shift_neg (n : ℝ)
    have h' : Summable (fun k : ℕ => |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 2) := by
      refine h.congr ?_; intro k; rw [← abs_inv, sq_abs]
    exact h'.mul_left 4
  -- per-term continuity on the ball
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun x : ℝ => if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2) t := by
    intro k
    by_cases hk : (k : ℤ) = n - 1
    · simp only [hk, if_pos]
      exact continuousOn_const
    · simp only [hk, if_neg, not_false_iff]
      apply ContinuousOn.pow
      apply ContinuousOn.inv₀
      · fun_prop
      · intro y hy hzero
        -- y = k+1, but k+1 ≠ n integer so y∉ball-only-n
        have hyeq : y = ((k + 1 : ℤ) : ℝ) := by
          have : y - ((k : ℝ) + 1) = 0 := by push_cast at hzero ⊢; linarith
          push_cast; linarith
        have := ball_half_int_eq hy hyeq.symm
        -- k+1 = n ⇒ k = n-1, contradiction
        apply hk; omega
  -- sup bound on the ball
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2‖
        ≤ (4 : ℝ) * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 2 := by
    intro k x hx
    by_cases hk : (k : ℤ) = n - 1
    · simp only [hk, if_pos, norm_zero]
      positivity
    · simp only [hk, if_neg, not_false_iff]
      -- |n − (k+1)| ≥ 1  (distinct integers n, k+1)
      have hdist : (1 : ℝ) ≤ |(n : ℝ) - (k + 1 : ℕ)| := by
        have hne : (n : ℤ) ≠ (k + 1 : ℕ) := by
          intro h; apply hk; omega
        have hcast : ((n - (k + 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) - (k + 1 : ℕ) := by push_cast; ring
        have h1 : (1 : ℤ) ≤ |(n - (k + 1 : ℕ) : ℤ)| :=
          Int.one_le_abs (sub_ne_zero.mpr hne)
        calc (1 : ℝ) ≤ (|(n - (k + 1 : ℕ) : ℤ)| : ℤ) := by exact_mod_cast h1
          _ = |((n - (k + 1 : ℕ) : ℤ) : ℝ)| := by rw [Int.cast_abs]
          _ = |(n : ℝ) - (k + 1 : ℕ)| := by rw [hcast]
      rw [Metric.mem_ball, Real.dist_eq] at hx
      -- |x − (k+1)| ≥ |n−(k+1)| − 1/2 ≥ |n−(k+1)|/2
      have hge : |(n : ℝ) - (k + 1 : ℕ)| / 2 ≤ |x - (k + 1 : ℕ)| := by
        have htri : |(n : ℝ) - (k + 1 : ℕ)| - |x - (n : ℝ)| ≤ |x - (k + 1 : ℕ)| := by
          have : |(n : ℝ) - (k + 1 : ℕ)| ≤ |x - (k + 1 : ℕ)| + |x - (n : ℝ)| := by
            calc |(n : ℝ) - (k + 1 : ℕ)|
                = |(x - (k + 1 : ℕ)) - (x - (n : ℝ))| := by ring_nf
              _ ≤ |x - (k + 1 : ℕ)| + |x - (n : ℝ)| := abs_sub _ _
          linarith
        have hxn : |x - (n : ℝ)| ≤ |(n : ℝ) - (k + 1 : ℕ)| / 2 := by
          linarith [hx]
        linarith
      have hxn_pos : 0 < |x - (k + 1 : ℕ)| :=
        lt_of_lt_of_le (by linarith) hge
      rw [Real.norm_eq_abs]
      have hb : |(x - (k + 1 : ℕ))⁻¹ ^ 2| = |x - (k + 1 : ℕ)|⁻¹ ^ 2 := by
        rw [← abs_inv, ← abs_pow]
      rw [hb]
      -- |x−(k+1)|⁻¹ ≤ 2·|n−(k+1)|⁻¹
      have hhalfpos : (0 : ℝ) < |(n : ℝ) - (k + 1 : ℕ)| / 2 := by
        have : (0:ℝ) < |(n : ℝ) - (k + 1 : ℕ)| := by linarith
        positivity
      have hinv : |x - (k + 1 : ℕ)|⁻¹ ≤ 2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ := by
        have := inv_anti₀ hhalfpos hge
        calc |x - (k + 1 : ℕ)|⁻¹ ≤ (|(n : ℝ) - (k + 1 : ℕ)| / 2)⁻¹ := this
          _ = 2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
      have hpow : |x - (k + 1 : ℕ)|⁻¹ ^ 2 ≤ (2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinv 2
      calc |x - (k + 1 : ℕ)|⁻¹ ^ 2 ≤ (2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹) ^ 2 := hpow
        _ = 4 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 2 := by ring
  have hcontOn : ContinuousOn
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2)) t :=
    continuousOn_tsum hcont hEnv hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds _ (by norm_num))

/-- **PROVEN.**  Positive analogue: for an integer `n`, the positive `^2`-tail with
the singular term `k = −n−1` removed is continuous at `x = n`.  (Same envelope
argument; the pole of the kept terms is `−(k+1) ≠ n`.) -/
theorem puncturedPosTail_continuousAt (n : ℤ) :
    ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)) (n : ℝ) := by
  classical
  set t : Set ℝ := Metric.ball (n : ℝ) (1 / 2) with ht
  have hEnv : Summable (fun k : ℕ => (4 : ℝ) * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 2) := by
    have h := summable_invSq_shift_pos (n : ℝ)
    have h' : Summable (fun k : ℕ => |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 2) := by
      refine h.congr ?_; intro k; rw [← abs_inv, sq_abs]
    exact h'.mul_left 4
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun x : ℝ => if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2) t := by
    intro k
    by_cases hk : (k : ℤ) = -n - 1
    · simp only [hk, if_pos]; exact continuousOn_const
    · simp only [hk, if_neg, not_false_iff]
      apply ContinuousOn.pow
      apply ContinuousOn.inv₀
      · fun_prop
      · intro y hy hzero
        have hyeq : y = ((-(k + 1) : ℤ) : ℝ) := by
          have : y + ((k : ℝ) + 1) = 0 := by push_cast at hzero ⊢; linarith
          push_cast; linarith
        have := ball_half_int_eq hy hyeq.symm
        apply hk; omega
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2‖
        ≤ (4 : ℝ) * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 2 := by
    intro k x hx
    by_cases hk : (k : ℤ) = -n - 1
    · simp only [hk, if_pos, norm_zero]; positivity
    · simp only [hk, if_neg, not_false_iff]
      have hdist : (1 : ℝ) ≤ |(n : ℝ) + (k + 1 : ℕ)| := by
        have hcast : ((n + ((k : ℤ) + 1) : ℤ) : ℝ) = (n : ℝ) + (k + 1 : ℕ) := by push_cast; ring
        have hnz : (n + ((k : ℤ) + 1) : ℤ) ≠ 0 := by
          intro h; apply hk; omega
        have h1 : (1 : ℤ) ≤ |(n + ((k : ℤ) + 1) : ℤ)| := Int.one_le_abs hnz
        calc (1 : ℝ) ≤ (|(n + ((k : ℤ) + 1) : ℤ)| : ℤ) := by exact_mod_cast h1
          _ = |((n + ((k : ℤ) + 1) : ℤ) : ℝ)| := by rw [Int.cast_abs]
          _ = |(n : ℝ) + (k + 1 : ℕ)| := by rw [hcast]
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hge : |(n : ℝ) + (k + 1 : ℕ)| / 2 ≤ |x + (k + 1 : ℕ)| := by
        have htri : |(n : ℝ) + (k + 1 : ℕ)| - |x - (n : ℝ)| ≤ |x + (k + 1 : ℕ)| := by
          have : |(n : ℝ) + (k + 1 : ℕ)| ≤ |x + (k + 1 : ℕ)| + |x - (n : ℝ)| := by
            calc |(n : ℝ) + (k + 1 : ℕ)|
                = |(x + (k + 1 : ℕ)) - (x - (n : ℝ))| := by ring_nf
              _ ≤ |x + (k + 1 : ℕ)| + |x - (n : ℝ)| := abs_sub _ _
          linarith
        have hxn : |x - (n : ℝ)| ≤ |(n : ℝ) + (k + 1 : ℕ)| / 2 := by
          linarith [hx]
        linarith
      have hxn_pos : 0 < |x + (k + 1 : ℕ)| := lt_of_lt_of_le (by linarith) hge
      rw [Real.norm_eq_abs]
      have hb : |(x + (k + 1 : ℕ))⁻¹ ^ 2| = |x + (k + 1 : ℕ)|⁻¹ ^ 2 := by
        rw [← abs_inv, ← abs_pow]
      rw [hb]
      have hhalfpos : (0 : ℝ) < |(n : ℝ) + (k + 1 : ℕ)| / 2 := by
        have : (0:ℝ) < |(n : ℝ) + (k + 1 : ℕ)| := by linarith
        positivity
      have hinv : |x + (k + 1 : ℕ)|⁻¹ ≤ 2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ := by
        have := inv_anti₀ hhalfpos hge
        calc |x + (k + 1 : ℕ)|⁻¹ ≤ (|(n : ℝ) + (k + 1 : ℕ)| / 2)⁻¹ := this
          _ = 2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
      have hpow : |x + (k + 1 : ℕ)|⁻¹ ^ 2 ≤ (2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinv 2
      calc |x + (k + 1 : ℕ)|⁻¹ ^ 2 ≤ (2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹) ^ 2 := hpow
        _ = 4 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 2 := by ring
  have hcontOn : ContinuousOn
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)) t :=
    continuousOn_tsum hcont hEnv hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds _ (by norm_num))

/-! ## §3 — `h3VaalerK` is the squared sinc kernel; continuity and integer values -/

/-- `h3VaalerK x = (sinc (π x))²`.  For `x = 0` both are `1`; for `x ≠ 0`,
`(sin πx/π)²·x⁻² = (sin πx/(πx))² = sinc(πx)²`. -/
theorem h3VaalerK_continuous : Continuous h3VaalerK := by
  rw [h3VaalerK_eq_sincSqPi_fun]
  exact sincSqPi_continuous

/-- `h3VaalerK 0 = 1`. -/
theorem h3VaalerK_zero : h3VaalerK 0 = 1 := by unfold h3VaalerK; simp

/-- For a nonzero integer `n`, `h3VaalerK n = 0` (`sin πn = 0`, `n ≠ 0`). -/
theorem h3VaalerK_int_ne_zero {n : ℤ} (hn : n ≠ 0) : h3VaalerK (n : ℝ) = 0 := by
  unfold h3VaalerK
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [if_neg hne]
  have hsin : Real.sin (π * (n : ℝ)) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi n
  rw [hsin]; ring

/-! ## §4 — Splitting the full tails into a punctured tail plus a single pole term -/

/-- Generic single-index extraction: for summable `g` and any `k₀`, the full tsum is
the punctured tsum (term `k₀` zeroed) plus `g k₀`. -/
theorem tsum_split_single {g : ℕ → ℝ} (hg : Summable g) (k₀ : ℕ) :
    (∑' k : ℕ, g k) = (∑' k : ℕ, (if k = k₀ then (0 : ℝ) else g k)) + g k₀ := by
  rw [hg.tsum_eq_add_tsum_ite k₀]; ring

/-- For an integer `n ≥ 1`, the negative tail splits as the (`k=n−1`-)punctured tail
plus the single pole `(x−n)⁻²`.  (The `(k:ℤ)=n−1` predicate equals `k=(n−1).toNat`.) -/
theorem negTail_split_pos {n : ℤ} (hn : 1 ≤ n) (x : ℝ) :
    h3NegTailSum x
      = (∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
        + (x - (n : ℝ))⁻¹ ^ 2 := by
  set k₀ : ℕ := (n - 1).toNat with hk₀
  have hk₀cast : ((k₀ : ℤ)) = n - 1 := by rw [hk₀]; omega
  have hcond : ∀ k : ℕ, ((k : ℤ) = n - 1) ↔ (k = k₀) := by
    intro k; constructor
    · intro h; omega
    · intro h; rw [h]; exact hk₀cast
  have hg : Summable (fun k : ℕ => (x - (k + 1 : ℕ))⁻¹ ^ 2) := summable_invSq_shift_neg x
  unfold h3NegTailSum
  rw [tsum_split_single hg k₀]
  congr 1
  · refine tsum_congr ?_; intro k
    by_cases h : (k : ℤ) = n - 1
    · rw [if_pos h, if_pos ((hcond k).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hcond k).mpr hh))]
  · -- g k₀ = (x − ((k₀)+1))⁻²  and  (k₀ : ℝ)+1 = n
    have : ((k₀ : ℝ) + 1) = (n : ℝ) := by
      have : (k₀ : ℤ) + 1 = n := by rw [hk₀cast]; ring
      exact_mod_cast this
    rw [show ((k₀ + 1 : ℕ) : ℝ) = (k₀ : ℝ) + 1 by push_cast; ring, this]

/-- For an integer `n ≤ -1`, the positive tail splits as the (`k=−n−1`-)punctured
tail plus the single pole `(x−n)⁻²` (here `x+(k+1)` at `k=−n−1` equals `x−n`). -/
theorem posTail_split_neg {n : ℤ} (hn : n ≤ -1) (x : ℝ) :
    h3TailSum x
      = (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))
        + (x - (n : ℝ))⁻¹ ^ 2 := by
  set k₀ : ℕ := (-n - 1).toNat with hk₀
  have hk₀cast : ((k₀ : ℤ)) = -n - 1 := by rw [hk₀]; omega
  have hcond : ∀ k : ℕ, ((k : ℤ) = -n - 1) ↔ (k = k₀) := by
    intro k; constructor
    · intro h; omega
    · intro h; rw [h]; exact hk₀cast
  have hg : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := summable_invSq_shift_pos x
  unfold h3TailSum
  rw [tsum_split_single hg k₀]
  congr 1
  · refine tsum_congr ?_; intro k
    by_cases h : (k : ℤ) = -n - 1
    · rw [if_pos h, if_pos ((hcond k).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hcond k).mpr hh))]
  · have hval : ((k₀ : ℝ) + 1) = -(n : ℝ) := by
      have : (k₀ : ℤ) + 1 = -n := by rw [hk₀cast]; ring
      exact_mod_cast this
    rw [show ((k₀ + 1 : ℕ) : ℝ) = (k₀ : ℝ) + 1 by push_cast; ring, hval]
    rw [show x + -(n : ℝ) = x - (n : ℝ) by ring]

/-- When `n ≥ 0`, the positive tail has no removed term: `PPos n = h3TailSum`. -/
theorem posTail_no_removal {n : ℤ} (hn : 0 ≤ n) (x : ℝ) :
    (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))
      = h3TailSum x := by
  unfold h3TailSum
  refine tsum_congr ?_
  intro k
  have hne : (k : ℤ) ≠ -n - 1 := by omega
  rw [if_neg hne]

/-- When `n ≤ 0`, the negative tail has no removed term: `PNeg n = h3NegTailSum`. -/
theorem negTail_no_removal {n : ℤ} (hn : n ≤ 0) (x : ℝ) :
    (∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
      = h3NegTailSum x := by
  unfold h3NegTailSum
  refine tsum_congr ?_
  intro k
  have hne : (k : ℤ) ≠ n - 1 := by omega
  rw [if_neg hne]

/-! ## §5 — The simple-pole cancellation `(sin πx/π)²·x⁻¹ = x·h3VaalerK x` -/

/-- `(sin πx/π)²·2x⁻¹ = 2x·h3VaalerK x` for `x ≠ 0` (shifted-Fejér at `m = 0`,
multiplied by `x`).  This handles the simple pole `2x⁻¹` of the bracket. -/
theorem sin_sq_two_inv_eq (x : ℝ) (hx : x ≠ 0) :
    (Real.sin (π * x) / π) ^ 2 * (2 * x⁻¹) = 2 * x * h3VaalerK x := by
  have hfej : (Real.sin (π * x) / π) ^ 2 * (x - ((0 : ℤ) : ℝ))⁻¹ ^ 2 = h3VaalerK (x - (0 : ℤ)) :=
    shifted_h3VaalerK_eq x 0 (by simpa using hx)
  simp only [Int.cast_zero, sub_zero] at hfej
  -- hfej : (sin/π)²·x⁻² = h3VaalerK x
  have hxinv : x * x⁻¹ ^ 2 = x⁻¹ := by
    rw [sq]; rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  have hkey : (Real.sin (π * x) / π) ^ 2 * (2 * x⁻¹)
      = 2 * x * ((Real.sin (π * x) / π) ^ 2 * (x⁻¹ ^ 2)) := by
    rw [show 2 * x * ((Real.sin (π * x) / π) ^ 2 * (x⁻¹ ^ 2))
        = 2 * (Real.sin (π * x) / π) ^ 2 * (x * x⁻¹ ^ 2) by ring, hxinv]
    ring
  rw [hkey, hfej]

/-- `Real.sign` at a positive integer is `1`. -/
private theorem sign_int_pos {n : ℤ} (hn : 1 ≤ n) : Real.sign (n : ℝ) = 1 :=
  Real.sign_of_pos (by exact_mod_cast (by omega : (0:ℤ) < n))

/-- `Real.sign` at a negative integer is `-1`. -/
private theorem sign_int_neg {n : ℤ} (hn : n ≤ -1) : Real.sign (n : ℝ) = -1 :=
  Real.sign_of_neg (by exact_mod_cast (by omega : (n:ℤ) < 0))

/-- Unified negative-tail split: `h3NegTailSum = PNeg n + (if 1 ≤ n then (x−n)⁻² else 0)`. -/
theorem negTail_unified_split (n : ℤ) (x : ℝ) :
    h3NegTailSum x
      = (∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
        + (if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0) := by
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, negTail_split_pos hn x]
  · rw [if_neg hn, add_zero, negTail_no_removal (by omega) x]

/-- Unified positive-tail split: `h3TailSum = PPos n + (if n ≤ -1 then (x−n)⁻² else 0)`. -/
theorem posTail_unified_split (n : ℤ) (x : ℝ) :
    h3TailSum x
      = (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))
        + (if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0) := by
  by_cases hn : n ≤ -1
  · rw [if_pos hn, posTail_split_neg hn x]
  · rw [if_neg hn, add_zero, posTail_no_removal (by omega) x]

/-- The signed singular contribution: `(sin πx/π)²·(S_neg − S_pos) = sgn(n)·h3VaalerK(x−n)`. -/
theorem sin_sq_singular_eq (n : ℤ) {x : ℝ} (hxn : x - (n : ℝ) ≠ 0) :
    (Real.sin (π * x) / π) ^ 2 *
        ((if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0)
          - (if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0))
      = Real.sign (n : ℝ) * h3VaalerK (x - (n : ℝ)) := by
  have hfej : (Real.sin (π * x) / π) ^ 2 * (x - (n : ℝ))⁻¹ ^ 2 = h3VaalerK (x - (n : ℝ)) := by
    have := shifted_h3VaalerK_eq x n hxn; simpa using this
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have hn1 : n ≤ -1 := by omega
    rw [if_neg (by omega : ¬ 1 ≤ n), if_pos hn1, sign_int_neg hn1]
    rw [zero_sub, mul_neg, hfej]; ring
  · subst hzero; simp
  · have hn1 : 1 ≤ n := by omega
    rw [if_pos hn1, if_neg (by omega : ¬ n ≤ -1), sign_int_pos hn1]
    rw [sub_zero, hfej]; ring

/-! ## §6 — Continuity of `h3InterpH` at the integers (the apparent-pole cancellation) -/

/-- The continuous candidate matching `h3InterpH` near `n`:
`Fcand n x = sgn(n)·h3VaalerK(x−n) + (sin πx/π)²·(PNeg n x − PPos n x) + 2x·h3VaalerK x`. -/
def Fcand (n : ℤ) (x : ℝ) : ℝ :=
  Real.sign (n : ℝ) * h3VaalerK (x - (n : ℝ))
    + (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
          - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)))
    + 2 * x * h3VaalerK x

/-- `Fcand n` is continuous at `(n : ℝ)`: a sum of `h3VaalerK` (continuous), the
continuous `(sin π·/π)²` times the two punctured tails (continuous at `n`), and the
continuous `2x·h3VaalerK x`. -/
theorem fcand_continuousAt (n : ℤ) : ContinuousAt (Fcand n) (n : ℝ) := by
  unfold Fcand
  have h1 : ContinuousAt (fun x : ℝ => Real.sign (n : ℝ) * h3VaalerK (x - (n : ℝ))) (n : ℝ) := by
    apply ContinuousAt.const_mul
    exact (h3VaalerK_continuous.comp (continuous_id.sub continuous_const)).continuousAt
  have hsinsq : ContinuousAt (fun x : ℝ => (Real.sin (π * x) / π) ^ 2) (n : ℝ) := by
    apply ContinuousAt.pow
    apply ContinuousAt.div_const
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
  have h2 : ContinuousAt
      (fun x : ℝ => (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
          - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))))
      (n : ℝ) :=
    hsinsq.mul ((puncturedNegTail_continuousAt n).sub (puncturedPosTail_continuousAt n))
  have h3 : ContinuousAt (fun x : ℝ => 2 * x * h3VaalerK x) (n : ℝ) := by
    apply ContinuousAt.mul
    · exact (continuousAt_const.mul continuousAt_id)
    · exact h3VaalerK_continuous.continuousAt
  exact (h1.add h2).add h3

/-- **PROVEN — `h3InterpH` is continuous at every integer.**  The apparent-pole
cancellation of Vaaler: near `n`, `h3InterpH = Fcand n` (the singular bracket term
`sgn(n)·(x−n)⁻²` collapses to `sgn(n)·h3VaalerK(x−n)` by `shifted_h3VaalerK_eq`, and the
simple pole `2x⁻¹` to `2x·h3VaalerK x`), and `Fcand n` is continuous at `n`. -/
theorem h3InterpH_continuousAt_int (n : ℤ) : ContinuousAt h3InterpH (n : ℝ) := by
  -- the candidate is eventually equal to h3InterpH near n
  have hEq : h3InterpH =ᶠ[nhds (n : ℝ)] Fcand n := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (n : ℝ) (show (0:ℝ) < 1/2 by norm_num)) ?_
    intro x hx
    by_cases hxn : x = (n : ℝ)
    · -- at the point: h3InterpH n = sign n = Fcand n n
      subst hxn
      have hsinn : Real.sin (π * (n : ℝ)) = 0 := by
        rw [mul_comm]; exact Real.sin_int_mul_pi n
      unfold h3InterpH Fcand
      rw [if_pos hsinn]
      rw [sub_self, h3VaalerK_zero]
      have hfejn : 2 * (n : ℝ) * h3VaalerK (n : ℝ) = 0 := by
        by_cases hn0 : n = 0
        · subst hn0; simp
        · rw [h3VaalerK_int_ne_zero hn0]; ring
      rw [hsinn]
      simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      rw [hfejn]; ring
    · -- off the point: x ∈ ball n (1/2), x ≠ n ⇒ x ∉ ℤ
      have hxnotint : x ∉ Set.range ((↑) : ℤ → ℝ) := by
        rintro ⟨m, hm⟩
        have := ball_half_int_eq hx hm
        rw [this] at hm; exact hxn hm.symm
      have hsin : Real.sin (π * x) ≠ 0 := h3Sin_pi_mul_ne_zero_of_notMem hxnotint
      have hx0 : x ≠ 0 := by
        intro h; apply hxnotint; exact ⟨0, by simp [h]⟩
      have hxn' : x - (n : ℝ) ≠ 0 := sub_ne_zero.mpr hxn
      -- shorthands for the two punctured tails
      set PN : ℝ := ∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2)
        with hPN
      set PP : ℝ := ∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)
        with hPP
      set Sn : ℝ := (if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0) with hSn
      set Sp : ℝ := (if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0) with hSp
      -- h3InterpH x = (sin/π)²·h3InterpBracket x
      unfold h3InterpH
      rw [if_neg hsin]
      -- expand h3InterpBracket via the unified splits
      have hbr : h3InterpBracket x = (PN + Sn) - (PP + Sp) + 2 * x⁻¹ := by
        unfold h3InterpBracket
        rw [show (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) = h3NegTailSum x from rfl]
        rw [show h3TailSum x = PP + Sp from posTail_unified_split n x]
        rw [show h3NegTailSum x = PN + Sn from negTail_unified_split n x]
      rw [hbr]
      -- distribute and use the two cancellation identities
      have hsing : (Real.sin (π * x) / π) ^ 2 * (Sn - Sp)
          = Real.sign (n : ℝ) * h3VaalerK (x - (n : ℝ)) := sin_sq_singular_eq n hxn'
      have hsimple : (Real.sin (π * x) / π) ^ 2 * (2 * x⁻¹) = 2 * x * h3VaalerK x :=
        sin_sq_two_inv_eq x hx0
      unfold Fcand
      -- LHS = (sin/π)²·((PN+Sn)-(PP+Sp)+2x⁻¹)
      --     = (sin/π)²·(PN-PP) + (sin/π)²·(Sn-Sp) + (sin/π)²·2x⁻¹
      rw [show (Real.sin (π * x) / π) ^ 2 * ((PN + Sn) - (PP + Sp) + 2 * x⁻¹)
          = (Real.sin (π * x) / π) ^ 2 * (PN - PP)
            + (Real.sin (π * x) / π) ^ 2 * (Sn - Sp)
            + (Real.sin (π * x) / π) ^ 2 * (2 * x⁻¹) by ring]
      rw [hsing, hsimple]
      ring
  -- conclude continuity by transporting along the eventual equality
  exact (continuousAt_congr hEq).mpr (fcand_continuousAt n)

/-- **PROVEN — `Continuous h3InterpH`.**  Off ℤ by the committed
`VaalerGRegularity` argument route (here re-derived from the same proven off-ℤ
continuity of the bracket factors), at ℤ by `h3InterpH_continuousAt_int`. -/
theorem h3InterpH_continuous : Continuous h3InterpH := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx : x₀ ∈ Set.range ((↑) : ℤ → ℝ)
  · obtain ⟨n, hn⟩ := hx
    rw [← hn]; exact h3InterpH_continuousAt_int n
  · -- off ℤ: h3InterpH = (sin/π)²·h3InterpBracket near x₀; both factors continuous off ℤ
    have hsin : Real.sin (π * x₀) ≠ 0 := h3Sin_pi_mul_ne_zero_of_notMem hx
    have hcontFactor : ContinuousAt
        (fun x : ℝ => (Real.sin (π * x) / π) ^ 2 * h3InterpBracket x) x₀ := by
      have h1 : ContinuousAt (fun x : ℝ => (Real.sin (π * x) / π) ^ 2) x₀ := by
        apply ContinuousAt.pow
        apply ContinuousAt.div_const
        exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
      exact h1.mul (h3InterpBracket_continuousAt hx)
    refine hcontFactor.congr ?_
    -- h3InterpH = the product on a neighbourhood of x₀ (sin ≠ 0 there)
    have hcont : ContinuousAt (fun z : ℝ => Real.sin (π * z)) x₀ :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    have hnhds : ∀ᶠ z : ℝ in nhds x₀, Real.sin (π * z) ≠ 0 := hcont.eventually_ne hsin
    filter_upwards [hnhds] with z hz
    unfold h3InterpH; rw [if_neg hz]


#print axioms h3InterpH_continuousAt_int
#print axioms h3InterpH_continuous

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerInterpHContinuous
