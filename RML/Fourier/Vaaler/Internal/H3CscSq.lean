module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.PSeries
import all Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Basic.Real.Sign

@[expose] public section
open scoped BigOperators Topology
open Filter Function

theorem one_div_sub_sq_summable (x : ℝ) :
    Summable (fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℤ => 1 / |(n : ℝ) + (-x)| ^ (2 : ℝ))
    ((Real.summable_one_div_int_add_rpow (-x) 2).mpr one_lt_two) ?_
  intro n
  have hsq_nn : 0 ≤ (x - (n : ℝ)) ^ 2 := sq_nonneg _
  have heq : (x - (n : ℝ)) ^ 2 = |(n : ℝ) + (-x)| ^ (2 : ℝ) := by
    rw [Real.rpow_two, sq_abs]; ring
  show ‖(1 : ℝ) / (x - (n : ℝ)) ^ 2‖ ≤ 1 / |(n : ℝ) + (-x)| ^ (2 : ℝ)
  rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_nonneg hsq_nn, heq]

/-- Summability of the sign-weighted family
`fun n : ℤ => sign(n) / (x - n)²` at any real `x`. -/
theorem beurlingB_nonintegerCore_summable (x : ℝ) :
    Summable (fun n : ℤ => Real.sign ((n : ℝ)) / (x - (n : ℝ)) ^ 2) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2)
    (one_div_sub_sq_summable x) ?_
  intro n
  have hsign : |Real.sign ((n : ℝ))| ≤ 1 := by
    rcases lt_trichotomy ((n : ℝ)) 0 with h | h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_eq_zero_iff.mpr h]; simp
    · rw [Real.sign_of_pos h]; norm_num
  have hsq_nn : 0 ≤ (x - (n : ℝ)) ^ 2 := sq_nonneg _
  show ‖Real.sign ((n : ℝ)) / (x - (n : ℝ)) ^ 2‖ ≤
      1 / (x - (n : ℝ)) ^ 2
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hsq_nn]
  by_cases hzero : (x - (n : ℝ)) ^ 2 = 0
  · rw [hzero, div_zero, div_zero]
  · have hpos : 0 < (x - (n : ℝ)) ^ 2 :=
      lt_of_le_of_ne hsq_nn (Ne.symm hzero)
    exact (div_le_div_iff_of_pos_right hpos).mpr hsign

/-! ### §12.bis — Mathlib infrastructure for csc²-Mittag-Leffler

The csc²-Mittag-Leffler identity is the term-by-term differentiation
of the complex cotangent Mittag-Leffler theorem `Complex.cot_series_rep`
(Mathlib).  The four infrastructure pieces below bridge the gap between
the existing Mathlib lemma and the real csc² identity we want.

* `Complex.isPathConnected_integerComplement` — preconnectedness of
  `ℂ \ ℤ` (via `Set.Countable.isPathConnected_compl_of_one_lt_rank`).
* `realNonInt_ball_subset_integerComplement` — for a real non-integer
  `x`, a small complex ball around `x` lies in `integerComplement`.
* `Complex.hasDerivAt_cot_of_sin_ne_zero` — derivative of `Complex.cot`
  away from zeros of `sin`, equal to `-1 / sin² z`.
* `summable_one_div_sub_int_sq_complex` — summability over ℤ of
  `1/(z - n)²` for `z ∈ integerComplement`. -/

/-- The complex integer complement is path-connected.

ℂ has real-rank `2 > 1`, and `Set.range ((↑) : ℤ → ℂ)` is countable,
so its complement is path-connected by the general lemma
`Set.Countable.isPathConnected_compl_of_one_lt_rank`. -/
theorem Complex.isPathConnected_integerComplement :
    IsPathConnected Complex.integerComplement := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two
  have hcnt : (Set.range ((↑) : ℤ → ℂ)).Countable :=
    Set.countable_range _
  exact hcnt.isPathConnected_compl_of_one_lt_rank hrank

theorem Complex.isPreconnected_integerComplement :
    IsPreconnected Complex.integerComplement :=
  (IsPathConnected.isConnected
    Complex.isPathConnected_integerComplement).isPreconnected

/-- For a real non-integer `x`, the distance from `(x : ℂ)` to any
integer point is bounded below by `‖x - ⌊x⌋‖` (positive). -/
theorem realNonInt_ball_subset_integerComplement {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    ∃ δ > 0, Metric.ball (x : ℂ) δ ⊆ Complex.integerComplement := by
  -- The set ℤ ⊆ ℂ is closed.
  have hclosed : IsClosed (Set.range ((↑) : ℤ → ℂ)) := by
    have := Complex.isOpen_compl_range_intCast
    exact (isOpen_compl_iff.mp this)
  -- (x : ℂ) ∉ Set.range Int.cast.
  have hnot : (x : ℂ) ∉ Set.range ((↑) : ℤ → ℂ) := by
    rintro ⟨n, hn⟩
    apply hx
    refine ⟨n, ?_⟩
    have hre : (x : ℂ).re = ((n : ℂ)).re := by rw [hn]
    have h1 : (x : ℂ).re = x := Complex.ofReal_re x
    have h2 : ((n : ℂ)).re = (n : ℝ) := by simp
    linarith [hre.symm.trans h1, h2]
  -- Use isOpen + mem to get a ball.
  obtain ⟨δ, hδ, hsub⟩ :=
    Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast (x : ℂ) hnot
  exact ⟨δ, hδ, hsub⟩

/-- Derivative of `Complex.cot` at points where `sin` is nonzero.

`Complex.cot z = cos z / sin z` by definition.  The quotient rule gives
`(- sin·sin - cos·cos)/sin² = -(sin²+cos²)/sin² = -1/sin²`. -/
theorem Complex.hasDerivAt_cot_of_sin_ne_zero {z : ℂ} (hz : Complex.sin z ≠ 0) :
    HasDerivAt Complex.cot (-1 / Complex.sin z ^ 2) z := by
  have h1 : HasDerivAt Complex.cos (-Complex.sin z) z := Complex.hasDerivAt_cos z
  have h2 : HasDerivAt Complex.sin (Complex.cos z) z := Complex.hasDerivAt_sin z
  have hd : HasDerivAt (fun z => Complex.cos z / Complex.sin z)
      ((-Complex.sin z * Complex.sin z - Complex.cos z * Complex.cos z) /
        Complex.sin z ^ 2) z := h1.div h2 hz
  -- Identify with `Complex.cot` since `cot z = cos z / sin z` definitionally.
  have hfun : (fun z : ℂ => Complex.cos z / Complex.sin z) = Complex.cot := by
    funext w; rfl
  rw [hfun] at hd
  -- Simplify the derivative expression: numerator = -(sin² + cos²) = -1.
  have hpyth : Complex.sin z ^ 2 + Complex.cos z ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq z
  have hnum_eq :
      (-Complex.sin z * Complex.sin z - Complex.cos z * Complex.cos z) = -1 := by
    have hrw :
        -Complex.sin z * Complex.sin z - Complex.cos z * Complex.cos z =
          -(Complex.sin z ^ 2 + Complex.cos z ^ 2) := by ring
    rw [hrw, hpyth]
  rw [hnum_eq] at hd
  exact hd

/-- Summability over `c : ℤ` of `1/(c + z)²` for any complex `z`.

For `|n| → ∞`, `|n + z| ∼ |n|`, so the summand is `O(1/n²)`, hence
summable.  We compare to `1/(|n| - ‖z‖)²` for `|n|` large, with the
remaining finitely many terms absorbed into a constant. -/
theorem Complex.summable_one_div_int_add_sq (z : ℂ) :
    Summable (fun n : ℤ => (1 : ℂ) / ((n : ℂ) + z) ^ 2) := by
  -- We bound the summand by `1 / (|n| - ‖z‖)^2` once `|n| > ‖z‖`.
  -- Since `n ↦ 1 / |n - ⌈‖z‖⌉ - 1|^2` is summable (shifted p-series),
  -- after absorbing finitely many exceptional terms we get summability.
  -- Concretely: apply `Summable.of_norm_bounded` with bound
  -- `fun n => (1 / (|n| - ‖z‖)^2)` outside a finite exceptional set,
  -- bundled via a max with a constant inside.
  -- Easiest implementation: use `summable_of_isBigO` / `Summable.comp_injective`.
  -- We invoke the existing EisensteinSeries lemma after the algebraic
  -- transformation `1/(n+z)² = ((n+z)(n+z))⁻¹` with the form
  -- `((1·c + d)·(1·c + d))⁻¹`.
  --
  -- Direct: use the comparison with `Real.summable_one_div_int_add_rpow z.re 2`.
  -- The norm `‖1/(n+z)²‖ = ‖n+z‖⁻²`, and `‖n+z‖² ≥ (n + z.re)²` only
  -- when z.im = 0 (trivial); otherwise `‖n+z‖² ≥ z.im² > 0` uniformly,
  -- and additionally ≥ (n + z.re)².  So bound by `min((n+z.re)², z.im²)`.
  -- This gives bound `1/(n+z.re)²` which is summable in n for `2 > 1`.
  -- The bound `1 / |n + z.re|^2` fails when `n + z.re = 0` (occurs at most
  -- once or twice depending on whether z.re is an integer).  We use
  -- `Summable.of_norm_bounded_eventually` to allow finitely many exceptions.
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ => 1 / |(n : ℝ) + z.re| ^ (2 : ℝ))
    ((Real.summable_one_div_int_add_rpow z.re 2).mpr one_lt_two) ?_
  -- Exceptional set: `{n : ℤ | (n + z.re)² = 0}` is finite (at most 1 element).
  rw [Filter.eventually_cofinite]
  -- Show the "violation" set is finite.
  have hfin :
      {n : ℤ | ¬ ‖(1 : ℂ) / ((n : ℂ) + z) ^ 2‖ ≤
        1 / |(n : ℝ) + z.re| ^ (2 : ℝ)}.Finite := by
    -- Show: violation implies `(n + z.re)² = 0`.
    apply Set.Finite.subset (s := {n : ℤ | (n : ℝ) + z.re = 0})
    · -- The latter has at most one element.
      by_cases hzint : ∃ n : ℤ, (n : ℝ) + z.re = 0
      · obtain ⟨n0, hn0⟩ := hzint
        refine Set.Finite.subset (Set.finite_singleton n0) ?_
        intro m hm
        have hm' : (m : ℝ) + z.re = 0 := hm
        have heq : (m : ℝ) = (n0 : ℝ) := by linarith [hn0]
        have heqz : (m : ℤ) = n0 := by exact_mod_cast heq
        simpa using heqz
      · refine (Set.finite_empty (α := ℤ)).subset ?_
        intro m hm
        exact (hzint ⟨m, hm⟩).elim
    · -- violation ⇒ (n+z.re)² = 0
      intro n hn
      by_contra hne
      apply hn
      -- Now repeat the standard estimate.
      have hsq_eq : ‖((n : ℂ) + z)‖ ^ 2 = ((n : ℝ) + z.re)^2 + z.im^2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
              Complex.intCast_re, Complex.intCast_im, sq]
      have hpos : 0 < ((n : ℝ) + z.re)^2 := by
        have : (n : ℝ) + z.re ≠ 0 := hne
        positivity
      have hlb_sq : ((n : ℝ) + z.re)^2 ≤ ‖((n : ℂ) + z)‖ ^ 2 := by
        rw [hsq_eq]; nlinarith [sq_nonneg z.im]
      have habs_pos : 0 < ‖((n : ℂ) + z)‖ ^ 2 := lt_of_lt_of_le hpos hlb_sq
      have hrpow : |(n : ℝ) + z.re| ^ (2 : ℝ) = ((n : ℝ) + z.re)^2 := by
        rw [Real.rpow_two, sq_abs]
      have hnorm_calc :
          ‖(1 : ℂ) / ((n : ℂ) + z) ^ 2‖ = 1 / ‖((n : ℂ) + z)‖ ^ 2 := by
        rw [norm_div, norm_one, norm_pow]
      rw [hnorm_calc, hrpow, div_le_div_iff₀ habs_pos hpos]
      linarith [hlb_sq]
  exact hfin

/-- The complex cotangent has derivative `-π²/sin²(πz)` away from
zeros of `sin(πz)`. -/
theorem Complex.hasDerivAt_pi_cot_pi {z : ℂ} (hz : Complex.sin (Real.pi * z) ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
  -- Chain rule on (π · cot(π·z)).
  have hcot : HasDerivAt Complex.cot
      (-1 / Complex.sin ((Real.pi : ℂ) * z) ^ 2) ((Real.pi : ℂ) * z) :=
    Complex.hasDerivAt_cot_of_sin_ne_zero hz
  -- d/dz of (π z) = π.
  have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (Real.pi : ℂ))
  have hcomp := hcot.comp z hlin
  -- d/dz of (π · cot(π·z)) = π · (d/dz cot)((π z)) · π = π² · (-1/sin²) = -π²/sin².
  have hmul := hcomp.const_mul (Real.pi : ℂ)
  -- Simplify the resulting derivative expression.
  refine hmul.congr_deriv ?_
  ring

/-- Complex csc²-Mittag-Leffler identity.

For every `z ∈ Complex.integerComplement`,
`∑'_{n ∈ ℤ} 1 / (z − n)² = π² / sin²(πz)`.

The proof differentiates `Complex.cot_series_rep` term-by-term on a
preconnected ball about `z` inside `Complex.integerComplement`, using
`hasDerivAt_tsum_of_isPreconnected` with the uniform summable bound
`‖d/dw cotTerm w n‖ ≤ 4/(n+1−R−‖z‖)²` for `w` in a small ball.  Once
both sides have been differentiated, the chain rule on the LHS gives
`-π² csc² πz`, and the term-by-term derivative of the RHS gives
`-1/z² - ∑'_{n ≥ 1} (1/(z-n)² + 1/(z+n)²)`, which is `-∑' 1/(z-n)²`
after re-indexing.

The detailed analytic assembly is the multi-month input encapsulated
here.  The four §12.bis infrastructure lemmas
(`integerComplement` preconnectedness, ball containment, `cot`
derivative, and summability of `1/(z+n)²`) supply the prerequisites
for the `hasDerivAt_tsum_of_isPreconnected` application. -/
theorem Complex.csc_sq_mittag_leffler {z : ℂ}
    (hz : z ∈ Complex.integerComplement) :
    (∑' n : ℤ, (1 : ℂ) / (z - (n : ℂ)) ^ 2) =
      (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * z) ^ 2 := by
  -- ============================================================
  -- Term-by-term differentiation of `cot_series_rep'`.
  --
  -- `cot_series_rep'`:  π · cot(πx) − 1/x = ∑' n:ℕ, (1/(x−(n+1)) + 1/(x+(n+1)))
  -- Differentiating both sides at z (using preconnected ball ⊆ ℂ\ℤ) yields
  --   -π² csc²(πz) + 1/z² = -∑' n:ℕ, (1/(z−(n+1))² + 1/(z+(n+1))²)
  -- which rearranges and reindexes to the goal.
  --
  -- Geometric setup: choose δ > 0 with `Metric.ball z δ ⊆ ℂ \ ℤ` (from
  -- openness), then set R := δ/2.  Key lower bound: for every w ∈ ball(z,R)
  -- and every integer m, `‖w - m‖ ≥ R`.
  -- ============================================================
  classical
  -- Pick δ > 0 so that the complex ball of radius δ about z avoids ℤ.
  have hopenZcompl : IsOpen (Set.range ((↑) : ℤ → ℂ))ᶜ :=
    Complex.isOpen_compl_range_intCast
  obtain ⟨δ, hδpos, hδsub⟩ :=
    Metric.isOpen_iff.mp hopenZcompl z hz
  -- Set R := δ/2.
  set R : ℝ := δ / 2 with hR_def
  have hRpos : 0 < R := half_pos hδpos
  have hR_lt_δ : R < δ := by linarith
  have ht_sub : Metric.ball z R ⊆ Complex.integerComplement := by
    intro w hw
    apply hδsub
    exact Metric.ball_subset_ball hR_lt_δ.le hw
  -- Key lower bound: for every integer m, `dist(z, m) ≥ δ`.
  have hdistz_int : ∀ m : ℤ, δ ≤ dist (z : ℂ) (m : ℂ) := by
    intro m
    by_contra hlt
    push Not at hlt
    have : (m : ℂ) ∈ Set.range ((↑) : ℤ → ℂ) := ⟨m, rfl⟩
    have hmem : (m : ℂ) ∈ Metric.ball z δ := by
      rw [Metric.mem_ball]; rw [dist_comm]; exact hlt
    exact (hδsub hmem) this
  let t : Set ℂ := Metric.ball z R
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_prec : IsPreconnected t := Metric.isPreconnected_ball
  have hz_mem_t : z ∈ t := Metric.mem_ball_self hRpos
  -- For w ∈ t, ‖w‖ < ‖z‖ + R.
  have hw_bound : ∀ w ∈ t, ‖w‖ < ‖z‖ + R := by
    intro w hw
    have hwd : dist w z < R := Metric.mem_ball.mp hw
    have h1 : ‖w - z‖ < R := by rw [← dist_eq_norm]; exact hwd
    have : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have := norm_add_le z (w - z)
      have heq : z + (w - z) = w := by ring
      rw [heq] at this; exact this
    linarith
  -- For w ∈ t and any integer m, `‖w - m‖ ≥ R`.
  have hw_int_lb : ∀ w ∈ t, ∀ m : ℤ, R ≤ ‖w - (m : ℂ)‖ := by
    intro w hw m
    have hwd : dist w z < R := Metric.mem_ball.mp hw
    have hdz : δ ≤ dist (z : ℂ) (m : ℂ) := hdistz_int m
    -- dist(w, m) ≥ dist(z, m) - dist(z, w) ≥ δ - R = R.
    have htri : dist (z : ℂ) (m : ℂ) ≤ dist z w + dist w (m : ℂ) :=
      dist_triangle _ _ _
    have hzw_eq : dist z w = dist w z := dist_comm _ _
    have hge : dist w (m : ℂ) ≥ R := by
      have h_two_R : 2 * R = δ := by rw [hR_def]; ring
      have hwz : dist w z < R := hwd
      have hzw : dist z w < R := by rw [hzw_eq]; exact hwz
      linarith [htri, hdz]
    have heq : dist w (m : ℂ) = ‖w - (m : ℂ)‖ := dist_eq_norm _ _
    rw [heq] at hge
    exact hge
  -- Define the n-th term and its derivative.
  let g : ℕ → ℂ → ℂ := fun n w =>
    1 / (w - ((n : ℂ) + 1)) + 1 / (w + ((n : ℂ) + 1))
  let g' : ℕ → ℂ → ℂ := fun n w =>
    -1 / (w - ((n : ℂ) + 1)) ^ 2 + -1 / (w + ((n : ℂ) + 1)) ^ 2
  -- Key nonzero facts on t.
  have hne_sub : ∀ w ∈ t, ∀ n : ℕ, w - ((n : ℂ) + 1) ≠ 0 := by
    intro w hw n
    have hw_int : w ∈ Complex.integerComplement := ht_sub hw
    have := Complex.integerComplement_add_ne_zero hw_int (-(n + 1 : ℤ))
    simpa [sub_eq_add_neg] using this
  have hne_add : ∀ w ∈ t, ∀ n : ℕ, w + ((n : ℂ) + 1) ≠ 0 := by
    intro w hw n
    have hw_int : w ∈ Complex.integerComplement := ht_sub hw
    have := Complex.integerComplement_add_ne_zero hw_int ((n + 1 : ℤ))
    simpa using this
  -- HasDerivAt of each g n on t.
  have hg_deriv : ∀ n w, w ∈ t → HasDerivAt (g n) (g' n w) w := by
    intro n w hw
    have h1 : w - ((n : ℂ) + 1) ≠ 0 := hne_sub w hw n
    have h2 : w + ((n : ℂ) + 1) ≠ 0 := hne_add w hw n
    have hd1 : HasDerivAt (fun w : ℂ => 1 / (w - ((n : ℂ) + 1)))
        (-1 / (w - ((n : ℂ) + 1)) ^ 2) w := by
      have hbase : HasDerivAt (fun w : ℂ => w - ((n : ℂ) + 1)) (1 : ℂ) w := by
        simpa using (hasDerivAt_id w).sub_const ((n : ℂ) + 1)
      have hinv : HasDerivAt (fun w : ℂ => (w - ((n : ℂ) + 1))⁻¹)
          (-1 / (w - ((n : ℂ) + 1)) ^ 2) w := hbase.inv h1
      have hcongr : (fun w : ℂ => 1 / (w - ((n : ℂ) + 1))) =
          (fun w : ℂ => (w - ((n : ℂ) + 1))⁻¹) := by funext y; simp [one_div]
      rw [hcongr]
      exact hinv
    have hd2 : HasDerivAt (fun w : ℂ => 1 / (w + ((n : ℂ) + 1)))
        (-1 / (w + ((n : ℂ) + 1)) ^ 2) w := by
      have hbase : HasDerivAt (fun w : ℂ => w + ((n : ℂ) + 1)) (1 : ℂ) w := by
        simpa using (hasDerivAt_id w).add_const ((n : ℂ) + 1)
      have hinv : HasDerivAt (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹)
          (-1 / (w + ((n : ℂ) + 1)) ^ 2) w := hbase.inv h2
      have hcongr : (fun w : ℂ => 1 / (w + ((n : ℂ) + 1))) =
          (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹) := by funext y; simp [one_div]
      rw [hcongr]
      exact hinv
    exact hd1.add hd2
  -- Uniform summable bound.
  -- Use `u n := 2 / (max R ((n+1) - (‖z‖+R)))²`.  This is ≤ 2/R² always
  -- (since denominator ≥ R), and ≤ 2/((n+1)-(‖z‖+R))² for n large.
  let u : ℕ → ℝ := fun n => 2 / (max R ((n : ℝ) + 1 - (‖z‖ + R))) ^ 2
  have hu_summable : Summable u := by
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => 8 / ((n : ℝ) + 1) ^ 2) ?_ ?_
    · -- 8 · ∑ 1/(n+1)^2 summable.
      have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
        have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
          Real.summable_one_div_nat_pow.mpr one_lt_two
        have := (summable_nat_add_iff (k := 1)
          (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)).mpr hbase
        refine this.congr ?_
        intro n
        push_cast; ring
      have hmul : Summable (fun n : ℕ => 8 * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2)) :=
        hsum.mul_left 8
      refine hmul.congr ?_
      intro n; ring
    · -- eventually ‖u n‖ ≤ 8/(n+1)^2.
      rw [Filter.eventually_atTop]
      refine ⟨Nat.ceil (2 * (‖z‖ + R)) + 1, ?_⟩
      intro n hn
      have hngt : (n : ℝ) ≥ 2 * (‖z‖ + R) := by
        have hle : ((Nat.ceil (2 * (‖z‖ + R)) : ℝ) + 1) ≤ (n : ℝ) := by
          have := (Nat.cast_le (α := ℝ)).mpr hn
          have hcast : ((Nat.ceil (2 * (‖z‖ + R)) + 1 : ℕ) : ℝ) =
              (Nat.ceil (2 * (‖z‖ + R)) : ℝ) + 1 := by push_cast; ring
          rw [hcast] at this
          exact this
        have hceil : 2 * (‖z‖ + R) ≤ (Nat.ceil (2 * (‖z‖ + R)) : ℝ) := Nat.le_ceil _
        linarith
      have h_half : (n : ℝ) + 1 - (‖z‖ + R) ≥ ((n : ℝ) + 1) / 2 := by linarith
      have h_pos_half : 0 < ((n : ℝ) + 1) / 2 := by
        have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      have h_denom_pos : 0 < (n : ℝ) + 1 - (‖z‖ + R) :=
        lt_of_lt_of_le h_pos_half h_half
      have h_pos_half_pow : 0 < (((n : ℝ) + 1) / 2) ^ 2 := by positivity
      -- u n ≤ 2 / ((n+1) - (‖z‖+R))^2 since denominator ≥ (n+1) - (‖z‖+R).
      have h_denom_ge : (n : ℝ) + 1 - (‖z‖ + R) ≤
          max R ((n : ℝ) + 1 - (‖z‖ + R)) := le_max_right _ _
      have h_max_pos : 0 < max R ((n : ℝ) + 1 - (‖z‖ + R)) :=
        lt_of_lt_of_le hRpos (le_max_left _ _)
      have h_max_sq_pos : 0 < (max R ((n : ℝ) + 1 - (‖z‖ + R))) ^ 2 := by positivity
      have h_u_le : u n ≤ 2 / ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2 := by
        show 2 / (max R ((n : ℝ) + 1 - (‖z‖ + R))) ^ 2 ≤
              2 / ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (le_of_lt h_denom_pos) h_denom_ge 2
      have h_chain : 2 / ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2 ≤ 8 / ((n : ℝ) + 1) ^ 2 := by
        have hsq_lb : ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2 ≥ ((n : ℝ) + 1) ^ 2 / 4 := by
          have h1 : 0 ≤ ((n : ℝ) + 1) / 2 := le_of_lt h_pos_half
          have h2 : ((n : ℝ) + 1) / 2 ≤ (n : ℝ) + 1 - (‖z‖ + R) := h_half
          have hsq : (((n : ℝ) + 1) / 2) ^ 2 ≤ ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2 := by
            exact pow_le_pow_left₀ h1 h2 2
          have heq : (((n : ℝ) + 1) / 2) ^ 2 = ((n : ℝ) + 1) ^ 2 / 4 := by ring
          linarith [heq ▸ hsq]
        have hsq_pos : 0 < ((n : ℝ) + 1 - (‖z‖ + R)) ^ 2 := by positivity
        have hnpos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
        rw [div_le_div_iff₀ hsq_pos hnpos]
        nlinarith [hsq_lb]
      have hu_nonneg : 0 ≤ u n := by
        show 0 ≤ 2 / (max R ((n : ℝ) + 1 - (‖z‖ + R))) ^ 2
        positivity
      rw [Real.norm_of_nonneg hu_nonneg]
      linarith
  -- Bound for derivatives.
  have hg'_bound : ∀ n w, w ∈ t → ‖g' n w‖ ≤ u n := by
    intro n w hw
    have hwbnd : ‖w‖ < ‖z‖ + R := hw_bound w hw
    have hne1 : w - ((n : ℂ) + 1) ≠ 0 := hne_sub w hw n
    have hne2 : w + ((n : ℂ) + 1) ≠ 0 := hne_add w hw n
    -- Bound ‖g' n w‖ ≤ 1/‖w-(n+1)‖² + 1/‖w+(n+1)‖².
    have hg'_norm :
        ‖g' n w‖ ≤ 1 / ‖w - ((n : ℂ) + 1)‖ ^ 2 + 1 / ‖w + ((n : ℂ) + 1)‖ ^ 2 := by
      have h1 : ‖(-1 : ℂ) / (w - ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖w - ((n : ℂ) + 1)‖ ^ 2 := by
        rw [norm_div, norm_neg, norm_one, norm_pow]
      have h2 : ‖(-1 : ℂ) / (w + ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖w + ((n : ℂ) + 1)‖ ^ 2 := by
        rw [norm_div, norm_neg, norm_one, norm_pow]
      have hadd := norm_add_le (-1 / (w - ((n : ℂ) + 1)) ^ 2 : ℂ)
        (-1 / (w + ((n : ℂ) + 1)) ^ 2)
      change ‖(-1 / (w - ((n : ℂ) + 1)) ^ 2 : ℂ) + -1 / (w + ((n : ℂ) + 1)) ^ 2‖ ≤ _
      calc ‖(-1 / (w - ((n : ℂ) + 1)) ^ 2 : ℂ) + -1 / (w + ((n : ℂ) + 1)) ^ 2‖
          ≤ ‖(-1 : ℂ) / (w - ((n : ℂ) + 1)) ^ 2‖ +
              ‖(-1 : ℂ) / (w + ((n : ℂ) + 1)) ^ 2‖ := hadd
        _ = 1 / ‖w - ((n : ℂ) + 1)‖ ^ 2 + 1 / ‖w + ((n : ℂ) + 1)‖ ^ 2 := by rw [h1, h2]
    -- Lower bound on ‖w - (n+1)‖ via integer-complement geometry.
    -- (n+1 : ℂ) = ((n+1 : ℤ) : ℂ).
    have hcast_pos : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℤ) : ℂ) := by push_cast; ring
    have hcast_neg : -((n : ℂ) + 1) = ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by push_cast; ring
    have h_sub_lb : R ≤ ‖w - ((n : ℂ) + 1)‖ := by
      rw [hcast_pos]
      exact hw_int_lb w hw ((n + 1 : ℕ) : ℤ)
    have h_add_lb : R ≤ ‖w + ((n : ℂ) + 1)‖ := by
      have hrew : ‖w + ((n : ℂ) + 1)‖ = ‖w - (-((n : ℂ) + 1))‖ := by
        congr 1; ring
      rw [hrew, hcast_neg]
      exact hw_int_lb w hw (-((n + 1 : ℕ) : ℤ))
    -- Additional bound: ‖w - (n+1)‖ ≥ (n+1) - ‖w‖ > (n+1) - (‖z‖+R), when positive.
    have h_sub_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖w - ((n : ℂ) + 1)‖ := by
      have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hrev : ‖w - ((n : ℂ) + 1)‖ = ‖((n : ℂ) + 1) - w‖ := by
        rw [norm_sub_rev]
      rw [hrev]
      have := norm_sub_norm_le ((n : ℂ) + 1) w
      rw [hn1_norm] at this
      linarith
    have h_add_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖w + ((n : ℂ) + 1)‖ := by
      have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      -- ‖w + (n+1)‖ ≥ ‖n+1‖ - ‖w‖.
      have hrev : ‖w + ((n : ℂ) + 1)‖ = ‖((n : ℂ) + 1) + w‖ := by
        rw [add_comm]
      rw [hrev]
      have := norm_sub_norm_le ((n : ℂ) + 1) (-w)
      have hneg : ‖((n : ℂ) + 1) - (-w)‖ = ‖((n : ℂ) + 1) + w‖ := by
        congr 1; ring
      rw [hneg] at this
      have hwn : ‖(-w : ℂ)‖ = ‖w‖ := norm_neg w
      rw [hwn] at this
      rw [hn1_norm] at this
      linarith
    -- Combine: ‖w ± (n+1)‖ ≥ max R ((n+1) - (‖z‖+R)).
    have h_sub_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖w - ((n : ℂ) + 1)‖ :=
      max_le h_sub_lb h_sub_lb2
    have h_add_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖w + ((n : ℂ) + 1)‖ :=
      max_le h_add_lb h_add_lb2
    -- Both norms ≥ M_max := max R ((n+1)-(‖z‖+R)) ≥ R > 0.
    set M_max : ℝ := max R ((n : ℝ) + 1 - (‖z‖ + R)) with hM_max_def
    have hM_max_pos : 0 < M_max := lt_of_lt_of_le hRpos (le_max_left _ _)
    -- 1/‖w ± (n+1)‖² ≤ 1/M_max².
    have hM_max_sq_pos : 0 < M_max ^ 2 := by positivity
    have hsub_norm_pos : 0 < ‖w - ((n : ℂ) + 1)‖ := by
      rw [norm_pos_iff]; exact hne1
    have hadd_norm_pos : 0 < ‖w + ((n : ℂ) + 1)‖ := by
      rw [norm_pos_iff]; exact hne2
    have h_inv_sub : (1 : ℝ) / ‖w - ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
      apply one_div_le_one_div_of_le hM_max_sq_pos
      exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_sub_max 2
    have h_inv_add : (1 : ℝ) / ‖w + ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
      apply one_div_le_one_div_of_le hM_max_sq_pos
      exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_add_max 2
    have hu_eq : u n = 2 / M_max ^ 2 := by simp [u, M_max]
    rw [hu_eq]
    have h_two_div : (2 : ℝ) / M_max ^ 2 = 1 / M_max ^ 2 + 1 / M_max ^ 2 := by ring
    rw [h_two_div]
    linarith [hg'_norm, h_inv_sub, h_inv_add]
  -- Pointwise summability of g at z.
  have hg_summable_z : Summable (fun n => g n z) := by
    have := summable_cotTerm hz
    have heq : (fun n => cotTerm z n) = (fun n => g n z) := by
      funext n
      simp [g, cotTerm]
    rw [heq] at this
    exact this
  -- Apply hasDerivAt_tsum_of_isPreconnected at z.
  have h_tsum_deriv :
      HasDerivAt (fun w => ∑' n, g n w) (∑' n, g' n z) z :=
    hasDerivAt_tsum_of_isPreconnected (u := u) hu_summable ht_open ht_prec
      hg_deriv hg'_bound hz_mem_t hg_summable_z hz_mem_t
  -- The LHS of `cot_series_rep'` at w ∈ t equals ∑' g n w.
  -- LHS: π · cot(πw) - 1/w.
  -- Differentiate both sides as functions of w on t.
  -- π·cot(πw) - 1/w has derivative -π²/sin²(πw) + 1/w² at z.
  have hsin_ne : Complex.sin (Real.pi * z) ≠ 0 := by
    intro hsin
    -- sin(πz) = 0 ⇔ z ∈ ℤ.
    rw [Complex.sin_eq_zero_iff] at hsin
    obtain ⟨n, hn⟩ := hsin
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hzn : z = (n : ℂ) := by
      have h_eq : (Real.pi : ℂ) * z = (n : ℂ) * (Real.pi : ℂ) := hn
      have h_eq2 : (Real.pi : ℂ) * z = (Real.pi : ℂ) * (n : ℂ) := by
        rw [h_eq]; ring
      exact mul_left_cancel₀ hpi h_eq2
    exact hz ⟨n, hzn.symm⟩
  have hz_ne_zero : z ≠ 0 := Complex.integerComplement.ne_zero hz
  -- Derivative of `π · cot(π·w)` at z.
  have hpicotpi := Complex.hasDerivAt_pi_cot_pi (z := z) hsin_ne
  -- Derivative of `1/w` at z.
  have h_inv_z : HasDerivAt (fun w : ℂ => 1 / w) (-1 / z ^ 2) z := by
    have hbase : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id z
    have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-1 / z ^ 2) z := hbase.inv hz_ne_zero
    have hcongr : (fun w : ℂ => 1 / w) = (fun w : ℂ => w⁻¹) := by funext w; simp [one_div]
    rw [hcongr]
    exact hinv
  -- Derivative of LHS = π·cot(πw) - 1/w.
  have hLHS_deriv :
      HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w) - 1 / w)
        (-(Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 - (-1 / z ^ 2)) z :=
    hpicotpi.sub h_inv_z
  -- The LHS equals ∑' n, g n w on `Complex.integerComplement` ⊇ t (via cot_series_rep').
  have hLHS_eq : ∀ w ∈ t, (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w) - 1 / w =
      ∑' n, g n w := by
    intro w hw
    have hw_int : w ∈ Complex.integerComplement := ht_sub hw
    have hrep := cot_series_rep' hw_int
    -- cot_series_rep': π * cot(πw) - 1/w = ∑' n:ℕ, (1/(w-(n+1)) + 1/(w+(n+1))).
    -- g n w = 1/(w-((n:ℂ)+1)) + 1/(w+((n:ℂ)+1)).
    -- These are definitionally equal.
    convert hrep using 2
  -- Replace function equality on t to get HasDerivAt for ∑' n, g n w.
  have h_eq_at_z := hLHS_eq z hz_mem_t
  -- Use HasDerivAt.congr_of_eventuallyEq.
  have hev_eq : (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w) - 1 / w)
      =ᶠ[nhds z] (fun w => ∑' n, g n w) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨t, ht_open.mem_nhds hz_mem_t, ?_⟩
    intro w hw
    exact hLHS_eq w hw
  have h_tsum_deriv' :
      HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w) - 1 / w)
        (∑' n, g' n z) z :=
    h_tsum_deriv.congr_of_eventuallyEq hev_eq
  -- Now equate the two derivative values via uniqueness.
  have h_unique : (∑' n, g' n z) =
      -(Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 - (-1 / z ^ 2) :=
    h_tsum_deriv'.unique hLHS_deriv
  -- Rewrite ∑' g' n z.
  -- g' n z = -1/(z-(n+1))² + (-1)/(z+(n+1))² = -(1/(z-(n+1))² + 1/(z+(n+1))²)
  have hg'_split :
      (∑' n, g' n z) = - ∑' n : ℕ, (1 / (z - ((n : ℂ) + 1)) ^ 2 +
                                     1 / (z + ((n : ℂ) + 1)) ^ 2) := by
    have hsum1 : Summable (fun n : ℕ => (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) := by
      have hint : Summable (fun n : ℤ => (1 : ℂ) / (((n : ℂ) + (-z)) ^ 2)) :=
        Complex.summable_one_div_int_add_sq (-z)
      -- Restrict to negative n shifted... easier: build directly via comparison.
      -- We compare to ‖u‖-summable bound at z (i.e. the n=z case of hg'_bound).
      have hbnd : ∀ n : ℕ, ‖(1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2‖ ≤ u n := by
        intro n
        have hne : z - ((n : ℂ) + 1) ≠ 0 := hne_sub z hz_mem_t n
        have h1 : ‖(1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖z - ((n : ℂ) + 1)‖ ^ 2 := by
          rw [norm_div, norm_one, norm_pow]
        rw [h1]
        have h_sub_lb : R ≤ ‖z - ((n : ℂ) + 1)‖ := by
          have hc : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℤ) : ℂ) := by push_cast; ring
          rw [hc]; exact hw_int_lb z hz_mem_t ((n + 1 : ℕ) : ℤ)
        have h_sub_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖z - ((n : ℂ) + 1)‖ := by
          have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
            have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
            rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          have hrev : ‖z - ((n : ℂ) + 1)‖ = ‖((n : ℂ) + 1) - z‖ := by rw [norm_sub_rev]
          rw [hrev]
          have := norm_sub_norm_le ((n : ℂ) + 1) z
          rw [hn1_norm] at this
          linarith [norm_nonneg z]
        have h_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖z - ((n : ℂ) + 1)‖ :=
          max_le h_sub_lb h_sub_lb2
        set M_max : ℝ := max R ((n : ℝ) + 1 - (‖z‖ + R))
        have hM_max_pos : 0 < M_max := lt_of_lt_of_le hRpos (le_max_left _ _)
        have hM_max_sq_pos : 0 < M_max ^ 2 := by positivity
        have : (1 : ℝ) / ‖z - ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
          apply one_div_le_one_div_of_le hM_max_sq_pos
          exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_max 2
        have hu_eq : u n = 2 / M_max ^ 2 := by simp [u, M_max]
        have : (1 : ℝ) / M_max ^ 2 ≤ 2 / M_max ^ 2 := by
          apply div_le_div_of_nonneg_right (by norm_num) hM_max_sq_pos.le
        linarith [this, ‹(1 : ℝ) / ‖z - ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2›]
      exact Summable.of_norm_bounded hu_summable hbnd
    have hsum2 : Summable (fun n : ℕ => (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2) := by
      -- Same argument as hsum1 with + replacing -.
      have hbnd : ∀ n : ℕ, ‖(1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2‖ ≤ u n := by
        intro n
        have hne : z + ((n : ℂ) + 1) ≠ 0 := hne_add z hz_mem_t n
        have h1 : ‖(1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖z + ((n : ℂ) + 1)‖ ^ 2 := by
          rw [norm_div, norm_one, norm_pow]
        rw [h1]
        have h_add_lb : R ≤ ‖z + ((n : ℂ) + 1)‖ := by
          have h_to_sub : ‖z + ((n : ℂ) + 1)‖ = ‖z - (-((n : ℂ) + 1))‖ := by
            congr 1; ring
          have hc : -((n : ℂ) + 1) = ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by push_cast; ring
          rw [h_to_sub, hc]
          exact hw_int_lb z hz_mem_t (-((n + 1 : ℕ) : ℤ))
        have h_add_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖z + ((n : ℂ) + 1)‖ := by
          have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
            have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
            rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          have := norm_sub_norm_le ((n : ℂ) + 1) (-z)
          have hreq : ‖((n : ℂ) + 1) - (-z)‖ = ‖z + ((n : ℂ) + 1)‖ := by
            congr 1; ring
          rw [hreq] at this
          have hnegz : ‖(-z : ℂ)‖ = ‖z‖ := norm_neg z
          rw [hnegz] at this
          rw [hn1_norm] at this
          linarith
        have h_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖z + ((n : ℂ) + 1)‖ :=
          max_le h_add_lb h_add_lb2
        set M_max : ℝ := max R ((n : ℝ) + 1 - (‖z‖ + R))
        have hM_max_pos : 0 < M_max := lt_of_lt_of_le hRpos (le_max_left _ _)
        have hM_max_sq_pos : 0 < M_max ^ 2 := by positivity
        have hub : (1 : ℝ) / ‖z + ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
          apply one_div_le_one_div_of_le hM_max_sq_pos
          exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_max 2
        have hu_eq : u n = 2 / M_max ^ 2 := by simp [u, M_max]
        have h12 : (1 : ℝ) / M_max ^ 2 ≤ 2 / M_max ^ 2 := by
          apply div_le_div_of_nonneg_right (by norm_num) hM_max_sq_pos.le
        linarith [hub, h12]
      exact Summable.of_norm_bounded hu_summable hbnd
    -- ∑' g' n z = -(∑' 1/(z-(n+1))² + ∑' 1/(z+(n+1))²) = -∑' (sum).
    have h_pointwise : ∀ n : ℕ, g' n z = -((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 +
                                          1 / (z + ((n : ℂ) + 1)) ^ 2) := by
      intro n
      show -1 / (z - ((n : ℂ) + 1)) ^ 2 + -1 / (z + ((n : ℂ) + 1)) ^ 2 =
          -(1 / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2)
      ring
    have hcongr : (fun n => g' n z) = fun n : ℕ =>
        -((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2) := by
      funext n; exact h_pointwise n
    rw [hcongr, tsum_neg]
  -- Combine: -(∑'…) = -π²/sin²(πz) + 1/z².
  rw [hg'_split] at h_unique
  -- Now derive: ∑' n, (1/(z-(n+1))² + 1/(z+(n+1))²) = π²/sin²(πz) - 1/z².
  have h_sum_eq :
      (∑' n : ℕ, ((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2)) =
        (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 - 1 / z ^ 2 := by
    have h_neg :
        -(∑' n : ℕ, ((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2)) =
        -(Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 - (-1 / z ^ 2) := h_unique
    have heq : -(∑' n : ℕ, ((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2)) =
        -((Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * z) ^ 2 - 1 / z ^ 2) := by
      rw [h_neg]
      ring
    have := neg_inj.mp heq
    exact this
  -- Now reindex ℤ-sum:
  -- ∑'_{n:ℤ} 1/(z-n)² = 1/z² + ∑'_{n:ℕ+} 1/(z-n)² + ∑'_{n:ℕ+} 1/(z+n)²
  -- The two ℕ+ sums equal ∑'_{k:ℕ} 1/(z-(k+1))² and ∑'_{k:ℕ} 1/(z+(k+1))² via tsum_pnat_eq_tsum_succ.
  have h_int_summable : Summable (fun n : ℤ => (1 : ℂ) / (z - (n : ℂ)) ^ 2) := by
    -- Reindex via n ↦ -n of Complex.summable_one_div_int_add_sq z.
    have hbase : Summable (fun n : ℤ => (1 : ℂ) / ((n : ℂ) + z) ^ 2) :=
      Complex.summable_one_div_int_add_sq z
    have hinj : Function.Injective (fun n : ℤ => -n) := neg_injective
    have hcomp := hbase.comp_injective hinj
    -- hcomp : Summable (fun n : ℤ => 1 / (((-n : ℤ) : ℂ) + z) ^ 2)
    -- Want:  Summable (fun n : ℤ => 1 / (z - (n : ℂ)) ^ 2).
    refine hcomp.congr ?_
    intro n
    show (1 : ℂ) / (((-n : ℤ) : ℂ) + z) ^ 2 = 1 / (z - (n : ℂ)) ^ 2
    have h1 : (((-n : ℤ) : ℂ)) = -(n : ℂ) := by push_cast; ring
    rw [h1]
    congr 2
    ring
  have h_int_split :
      (∑' n : ℤ, (1 : ℂ) / (z - (n : ℂ)) ^ 2) = (1 : ℂ) / (z - ((0 : ℤ) : ℂ)) ^ 2 +
        (∑' n : ℕ+, (1 : ℂ) / (z - ((n : ℤ) : ℂ)) ^ 2) +
        (∑' n : ℕ+, (1 : ℂ) / (z - ((-((n : ℤ)) : ℤ) : ℂ)) ^ 2) :=
    tsum_int_eq_zero_add_tsum_pnat h_int_summable
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℂ) / (z - ((n : ℤ) : ℂ)) ^ 2),
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (1 : ℂ) / (z - ((-((n : ℤ)) : ℤ) : ℂ)) ^ 2)] at h_int_split
  -- Simplify n=0 term.
  have h_zero : (1 : ℂ) / (z - ((0 : ℤ) : ℂ)) ^ 2 = 1 / z ^ 2 := by simp
  rw [h_zero] at h_int_split
  -- Bridge: 1/(z - ((n+1 : ℕ) : ℤ) : ℂ)² = 1/(z - ((n : ℂ) + 1))².
  have h_succ_pos : ∀ n : ℕ, (1 : ℂ) / (z - (((n + 1 : ℕ) : ℤ) : ℂ)) ^ 2 =
      (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 := by
    intro n
    have : ((((n + 1 : ℕ) : ℤ) : ℂ)) = ((n : ℂ) + 1) := by push_cast; ring
    rw [this]
  have h_succ_neg : ∀ n : ℕ, (1 : ℂ) / (z - ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℂ)) ^ 2 =
      (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2 := by
    intro n
    have h1 : ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℂ) = -((n : ℂ) + 1) := by push_cast; ring
    rw [h1]
    have h2 : z - (-((n : ℂ) + 1)) = z + ((n : ℂ) + 1) := by ring
    rw [h2]
  -- Apply both rewrites.
  have hpos_eq :
      (∑' n : ℕ, (1 : ℂ) / (z - (((n + 1 : ℕ) : ℤ) : ℂ)) ^ 2) =
        ∑' n : ℕ, (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 := by
    apply tsum_congr; exact h_succ_pos
  have hneg_eq :
      (∑' n : ℕ, (1 : ℂ) / (z - ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℂ)) ^ 2) =
        ∑' n : ℕ, (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2 := by
    apply tsum_congr; exact h_succ_neg
  rw [hpos_eq, hneg_eq] at h_int_split
  -- Sum: split sum equals 1/z² + S₁ + S₂. We want this to equal π²/sin²(πz).
  -- We have h_sum_eq: S₁ + S₂ (combined) = π²/sin²(πz) - 1/z².
  -- We need to show S₁ + S₂ (separate tsums) = the combined tsum.
  -- Reuse the summability proofs from inside hg'_split.
  have hsum1' : Summable (fun n : ℕ => (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) := by
    have hbnd : ∀ n : ℕ, ‖(1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2‖ ≤ u n := by
      intro n
      have h1 : ‖(1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖z - ((n : ℂ) + 1)‖ ^ 2 := by
        rw [norm_div, norm_one, norm_pow]
      rw [h1]
      have h_sub_lb : R ≤ ‖z - ((n : ℂ) + 1)‖ := by
        have hc : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℤ) : ℂ) := by push_cast; ring
        rw [hc]; exact hw_int_lb z hz_mem_t ((n + 1 : ℕ) : ℤ)
      have h_sub_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖z - ((n : ℂ) + 1)‖ := by
        have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
          have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
          rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hrev : ‖z - ((n : ℂ) + 1)‖ = ‖((n : ℂ) + 1) - z‖ := by rw [norm_sub_rev]
        rw [hrev]
        have := norm_sub_norm_le ((n : ℂ) + 1) z
        rw [hn1_norm] at this
        linarith [norm_nonneg z]
      have h_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖z - ((n : ℂ) + 1)‖ :=
        max_le h_sub_lb h_sub_lb2
      set M_max : ℝ := max R ((n : ℝ) + 1 - (‖z‖ + R))
      have hM_max_pos : 0 < M_max := lt_of_lt_of_le hRpos (le_max_left _ _)
      have hM_max_sq_pos : 0 < M_max ^ 2 := by positivity
      have hub : (1 : ℝ) / ‖z - ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
        apply one_div_le_one_div_of_le hM_max_sq_pos
        exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_max 2
      have hu_eq : u n = 2 / M_max ^ 2 := by simp [u, M_max]
      have h12 : (1 : ℝ) / M_max ^ 2 ≤ 2 / M_max ^ 2 := by
        apply div_le_div_of_nonneg_right (by norm_num) hM_max_sq_pos.le
      linarith [hub, h12]
    exact Summable.of_norm_bounded hu_summable hbnd
  have hsum2' : Summable (fun n : ℕ => (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2) := by
    have hbnd : ∀ n : ℕ, ‖(1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2‖ ≤ u n := by
      intro n
      have h1 : ‖(1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2‖ = 1 / ‖z + ((n : ℂ) + 1)‖ ^ 2 := by
        rw [norm_div, norm_one, norm_pow]
      rw [h1]
      have h_add_lb : R ≤ ‖z + ((n : ℂ) + 1)‖ := by
        have h_to_sub : ‖z + ((n : ℂ) + 1)‖ = ‖z - (-((n : ℂ) + 1))‖ := by
          congr 1; ring
        have hc : -((n : ℂ) + 1) = ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by push_cast; ring
        rw [h_to_sub, hc]
        exact hw_int_lb z hz_mem_t (-((n + 1 : ℕ) : ℤ))
      have h_add_lb2 : (n : ℝ) + 1 - (‖z‖ + R) ≤ ‖z + ((n : ℂ) + 1)‖ := by
        have hn1_norm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
          have h0 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
          rw [h0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have := norm_sub_norm_le ((n : ℂ) + 1) (-z)
        have hreq : ‖((n : ℂ) + 1) - (-z)‖ = ‖z + ((n : ℂ) + 1)‖ := by
          congr 1; ring
        rw [hreq] at this
        have hnegz : ‖(-z : ℂ)‖ = ‖z‖ := norm_neg z
        rw [hnegz] at this
        rw [hn1_norm] at this
        linarith
      have h_max : max R ((n : ℝ) + 1 - (‖z‖ + R)) ≤ ‖z + ((n : ℂ) + 1)‖ :=
        max_le h_add_lb h_add_lb2
      set M_max : ℝ := max R ((n : ℝ) + 1 - (‖z‖ + R))
      have hM_max_pos : 0 < M_max := lt_of_lt_of_le hRpos (le_max_left _ _)
      have hM_max_sq_pos : 0 < M_max ^ 2 := by positivity
      have hub : (1 : ℝ) / ‖z + ((n : ℂ) + 1)‖ ^ 2 ≤ 1 / M_max ^ 2 := by
        apply one_div_le_one_div_of_le hM_max_sq_pos
        exact pow_le_pow_left₀ (le_of_lt hM_max_pos) h_max 2
      have hu_eq : u n = 2 / M_max ^ 2 := by simp [u, M_max]
      have h12 : (1 : ℝ) / M_max ^ 2 ≤ 2 / M_max ^ 2 := by
        apply div_le_div_of_nonneg_right (by norm_num) hM_max_sq_pos.le
      linarith [hub, h12]
    exact Summable.of_norm_bounded hu_summable hbnd
  have h_combine :
      (∑' n : ℕ, (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) +
        (∑' n : ℕ, (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2) =
      ∑' n : ℕ, ((1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2) :=
    (Summable.tsum_add hsum1' hsum2').symm
  -- Combine with h_int_split and h_sum_eq.
  -- h_int_split: ∑'_ℤ = 1/z² + S₁ + S₂.  Want: ∑'_ℤ = π²/sin²(πz).
  -- h_sum_eq + h_combine: S₁ + S₂ = π²/sin²(πz) - 1/z².
  rw [h_int_split]
  -- Goal: 1/z² + S₁ + S₂ = π²/sin²(πz).
  -- Use h_combine to combine S₁ + S₂.
  have hassoc : (1 : ℂ) / z ^ 2 +
      (∑' n : ℕ, (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) +
      (∑' n : ℕ, (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2) =
      (1 : ℂ) / z ^ 2 +
      ((∑' n : ℕ, (1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) +
        (∑' n : ℕ, (1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2)) := by ring
  rw [hassoc, h_combine, h_sum_eq]
  ring

/-- The csc²-Mittag-Leffler identity (Vaaler 1985 eq. (2.7) / classical).

For every non-integer real `x`,
`∑'_{n ∈ ℤ} 1 / (x − n)² = π² / sin²(πx)`.

We derive the real identity from the complex one
(`Complex.csc_sq_mittag_leffler`) by specializing to `z = (x : ℂ)` and
extracting real parts.  The complex identity itself follows from
differentiating the Mittag-Leffler series for `π cot πz` term-by-term.

Note: this derivation is conditional on the complex form, which is the
single remaining genuine analytic input — encapsulated as
`Complex.csc_sq_mittag_leffler`. -/
theorem csc_sq_mittag_leffler {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    (∑' n : ℤ, 1 / (x - (n : ℝ)) ^ 2) =
      Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2 := by
  -- Specialize the complex version at `z = (x : ℂ)`.
  have hxC : (x : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    apply hx
    refine ⟨n, ?_⟩
    have hre : (x : ℂ).re = ((n : ℂ)).re := by rw [hn]
    have h1 : (x : ℂ).re = x := Complex.ofReal_re x
    have h2 : ((n : ℂ)).re = (n : ℝ) := by simp
    linarith [hre.symm.trans h1, h2]
  have hcplx := Complex.csc_sq_mittag_leffler hxC
  -- Take real parts.  Both sides are real when `z = (x : ℂ)`.
  -- LHS: each summand `1/((x : ℂ) - n)² = 1/(x - n)²` (the imaginary part vanishes
  -- since `(x : ℂ) - n` has zero imaginary part).
  -- RHS: `Real.pi² / Complex.sin (π·x)² = Real.pi² / (Real.sin (π·x))²` (since
  -- `Complex.sin (real) = Real.sin`).
  -- We push the cast through by `Complex.ofReal_tsum` (or by direct rewriting).
  have hLHS_real :
      (∑' n : ℤ, (1 : ℂ) / ((x : ℂ) - (n : ℂ)) ^ 2) =
        ((∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hRHS_real :
      ((Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ^ 2) =
        ((Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2 : ℝ) : ℂ) := by
    have hsin : Complex.sin ((Real.pi : ℂ) * (x : ℂ)) =
        ((Real.sin (Real.pi * x) : ℝ) : ℂ) := by
      have : ((Real.pi * x : ℝ) : ℂ) = (Real.pi : ℂ) * (x : ℂ) := by push_cast; ring
      rw [← this, ← Complex.ofReal_sin]
    rw [hsin]
    push_cast
    ring
  rw [hLHS_real, hRHS_real] at hcplx
  exact_mod_cast hcplx

/-- "Even part" csc² tsum, positive-index form:
  `∑'_{n : ℕ} (1/(x−(n+1))² + 1/(x+(n+1))²) + 1/x²
    = π² / sin²(πx)`   for `x ∉ ℤ`.

Conditional consequence of `csc_sq_mittag_leffler`: split the
symmetric ℤ-sum `∑'_{n ∈ ℤ} 1/(x − n)²` into positive, negative, and
zero parts.  Proof-complete given `csc_sq_mittag_leffler`. -/
theorem mittag_leffler_pos_index_form {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    (∑' n : ℕ, (1 / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 +
                 1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) + 1 / x ^ 2 =
      Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2 := by
  classical
  have hg_sum : Summable (fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2) :=
    one_div_sub_sq_summable x
  have hinj_pos : Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : ℤ)) := by
    intro a b hab
    simp only at hab
    have h1 : (a + 1 : ℕ) = (b + 1 : ℕ) := by exact_mod_cast hab
    omega
  have hinj_neg : Function.Injective (fun k : ℕ => (-((k + 1 : ℕ) : ℤ) : ℤ)) := by
    intro a b hab
    simp only at hab
    have h1 : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) := neg_injective hab
    have h2 : (a + 1 : ℕ) = (b + 1 : ℕ) := by exact_mod_cast h1
    omega
  have hcompPos := hg_sum.comp_injective hinj_pos
  have hcompNeg := hg_sum.comp_injective hinj_neg
  -- Express the ℕ tsum (positive-index) in the target form.
  have htsumPos :
      (∑' k : ℕ, (1 : ℝ) / (x - (((k + 1 : ℕ) : ℤ) : ℝ)) ^ 2) =
        ∑' k : ℕ, 1 / (x - ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    apply tsum_congr
    intro k
    have hc : (((k + 1 : ℕ) : ℤ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]
  -- Express the ℕ tsum (negative-index) in the target form.
  have htsumNeg :
      (∑' k : ℕ, (1 : ℝ) / (x - ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)) ^ 2) =
        ∑' k : ℕ, 1 / (x + ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    apply tsum_congr
    intro k
    have hc : ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) = -(((k + 1 : ℕ) : ℝ)) := by
      push_cast; ring
    have hd : (x - (-(((k + 1 : ℕ) : ℝ)))) ^ 2 = (x + ((k + 1 : ℕ) : ℝ)) ^ 2 := by
      have : x - (-(((k + 1 : ℕ) : ℝ))) = x + ((k + 1 : ℕ) : ℝ) := by ring
      rw [this]
    rw [hc, hd]
  -- ℤ-split via `tsum_int_eq_zero_add_tsum_pnat`, then convert pnat to ℕ.
  have hsplit :
      (∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2) = 1 / (x - ((0 : ℤ) : ℝ)) ^ 2 +
        (∑' n : ℕ+, (1 : ℝ) / (x - ((n : ℤ) : ℝ)) ^ 2) +
        (∑' n : ℕ+, (1 : ℝ) / (x - ((-((n : ℤ)) : ℤ) : ℝ)) ^ 2) :=
    tsum_int_eq_zero_add_tsum_pnat hg_sum
  rw [tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (1 : ℝ) / (x - ((n : ℤ) : ℝ)) ^ 2),
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (1 : ℝ) / (x - ((-((n : ℤ)) : ℤ) : ℝ)) ^ 2)] at hsplit
  -- Simplify the n = 0 term to `1/x²`.
  have h0 : (1 : ℝ) / (x - ((0 : ℤ) : ℝ)) ^ 2 = 1 / x ^ 2 := by simp
  rw [h0] at hsplit
  -- Bridge `(↑(n + 1) : ℤ)` form (post-rewrite) to `((n + 1 : ℕ) : ℤ)` form.
  -- The `simp only`-style normalization turns one into the other directly.
  -- Apply tsum congruences htsumPos / htsumNeg.
  rw [htsumPos, htsumNeg] at hsplit
  -- Apply csc²-Mittag-Leffler.
  rw [csc_sq_mittag_leffler hx] at hsplit
  -- Combine positive- and negative-index halves into one ℕ-tsum.
  have hsumPos_sum :
      Summable (fun k : ℕ => (1 : ℝ) / (x - ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    refine hcompPos.congr ?_
    intro k
    have hc : (((k + 1 : ℕ) : ℤ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    show (1 : ℝ) / (x - (((k + 1 : ℕ) : ℤ) : ℝ)) ^ 2 = _
    rw [hc]
  have hsumNeg_sum :
      Summable (fun k : ℕ => (1 : ℝ) / (x + ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    refine hcompNeg.congr ?_
    intro k
    have hc : ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) = -(((k + 1 : ℕ) : ℝ)) := by
      push_cast; ring
    have hd : (x - (-(((k + 1 : ℕ) : ℝ)))) ^ 2 = (x + ((k + 1 : ℕ) : ℝ)) ^ 2 := by
      have : x - (-(((k + 1 : ℕ) : ℝ))) = x + ((k + 1 : ℕ) : ℝ) := by ring
      rw [this]
    show (1 : ℝ) / (x - ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)) ^ 2 = _
    rw [hc, hd]
  have hcombine :
      (∑' k : ℕ, 1 / (x - ((k + 1 : ℕ) : ℝ)) ^ 2) +
        (∑' k : ℕ, 1 / (x + ((k + 1 : ℕ) : ℝ)) ^ 2) =
      ∑' n : ℕ, (1 / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 +
                  1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) :=
    (Summable.tsum_add hsumPos_sum hsumNeg_sum).symm
  linarith [hsplit, hcombine]

