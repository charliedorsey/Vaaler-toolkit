module

public import RML.Fourier.Vaaler.Internal.H3CscSq
public import RML.Fourier.Vaaler.Internal.H3VaalerCoeff

@[expose] public section

open scoped BigOperators Topology
open Filter Function

namespace RML.Fourier.Vaaler.Internal

noncomputable def h3VaalerCore (x : ℝ) : ℝ :=
  (∑' n : ℤ, Real.sign (n : ℝ) / (x - (n : ℝ)) ^ 2) + 2 / x

noncomputable def h3VaalerH (x : ℝ) : ℝ := by
  classical
  exact
    if h : ∃ m : ℤ, x = (m : ℝ) then
      Real.sign ((Classical.choose h : ℤ) : ℝ)
    else
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 * h3VaalerCore x

noncomputable def h3VaalerK (x : ℝ) : ℝ :=
  if x = 0 then 1 else
    (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2

theorem h3VaalerH_intCast (m : ℤ) :
    h3VaalerH (m : ℝ) = Real.sign ((m : ℝ)) := by
  classical
  have h : ∃ n : ℤ, (m : ℝ) = (n : ℝ) := ⟨m, rfl⟩
  unfold h3VaalerH
  simp only [h, dif_pos]
  have hk : ((Classical.choose h : ℤ) : ℝ) = (m : ℝ) :=
    (Classical.choose_spec h).symm
  rw [hk]

@[simp] theorem h3VaalerH_zero : h3VaalerH 0 = 0 := by
  simpa using h3VaalerH_intCast 0

@[simp] theorem h3VaalerK_zero : h3VaalerK 0 = 1 := by
  simp [h3VaalerK]

theorem h3VaalerK_nonneg (x : ℝ) : 0 ≤ h3VaalerK x := by
  unfold h3VaalerK
  split_ifs
  · exact zero_le_one
  · positivity

theorem h3VaalerK_neg (x : ℝ) : h3VaalerK (-x) = h3VaalerK x := by
  unfold h3VaalerK
  by_cases hx : x = 0
  · subst x
    simp
  · have hxn : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [if_neg hxn, if_neg hx]
    have hsin : Real.sin (Real.pi * (-x)) = -Real.sin (Real.pi * x) := by
      rw [mul_neg, Real.sin_neg]
    have hden : Real.pi * (-x) = -(Real.pi * x) := by ring
    rw [hsin, hden, neg_div_neg_eq]

theorem h3VaalerCore_neg (x : ℝ) :
    h3VaalerCore (-x) = -h3VaalerCore x := by
  unfold h3VaalerCore
  have hreindex :
      (∑' n : ℤ, Real.sign ((n : ℝ)) / (-x - (n : ℝ)) ^ 2) =
        ∑' n : ℤ,
          Real.sign (((-n : ℤ) : ℝ)) /
            (-x - ((-n : ℤ) : ℝ)) ^ 2 := by
    exact (Equiv.tsum_eq (Equiv.neg ℤ) _).symm
  rw [hreindex]
  have hterm : ∀ n : ℤ,
      Real.sign (((-n : ℤ) : ℝ)) / (-x - ((-n : ℤ) : ℝ)) ^ 2 =
        -(Real.sign ((n : ℝ)) / (x - (n : ℝ)) ^ 2) := by
    intro n
    have hcast : (((-n : ℤ) : ℝ)) = -(n : ℝ) := by push_cast; ring
    rw [hcast, Real.sign_neg]
    have hsq : (-x - -(n : ℝ)) ^ 2 = (x - (n : ℝ)) ^ 2 := by ring
    rw [hsq]
    ring
  simp_rw [hterm]
  rw [tsum_neg]
  have htwo : (2 : ℝ) / (-x) = -(2 / x) := by
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  rw [htwo]
  ring

theorem h3VaalerH_neg (x : ℝ) :
    h3VaalerH (-x) = -h3VaalerH x := by
  classical
  by_cases hx : ∃ m : ℤ, x = (m : ℝ)
  · obtain ⟨m, rfl⟩ := hx
    have hcast : -((m : ℤ) : ℝ) = (((-m : ℤ) : ℝ)) := by push_cast; ring
    rw [hcast, h3VaalerH_intCast, h3VaalerH_intCast]
    push_cast
    exact Real.sign_neg
  · have hxneg : ¬ ∃ m : ℤ, (-x) = (m : ℝ) := by
      rintro ⟨m, hm⟩
      apply hx
      refine ⟨-m, ?_⟩
      push_cast at hm ⊢
      linarith
    have hH : h3VaalerH x =
        (Real.sin (Real.pi * x) / Real.pi) ^ 2 * h3VaalerCore x := by
      unfold h3VaalerH
      simp [hx]
    have hHneg : h3VaalerH (-x) =
        (Real.sin (Real.pi * (-x)) / Real.pi) ^ 2 * h3VaalerCore (-x) := by
      unfold h3VaalerH
      simp [hxneg]
    rw [hH, hHneg, h3VaalerCore_neg]
    have hsin : Real.sin (Real.pi * (-x)) = -Real.sin (Real.pi * x) := by
      rw [mul_neg, Real.sin_neg]
    rw [hsin]
    ring

theorem h3_one_div_sub_succ_sq_summable (x : ℝ) :
    Summable (fun n : ℕ =>
      (1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  classical
  have hg_sum : Summable (fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2) :=
    one_div_sub_sq_summable x
  have hinj_pos : Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : ℤ)) := by
    intro a b hab
    simp only at hab
    have h1 : (a + 1 : ℕ) = (b + 1 : ℕ) := by exact_mod_cast hab
    omega
  have hcompPos := hg_sum.comp_injective hinj_pos
  refine hcompPos.congr ?_
  intro k
  have hc : (((k + 1 : ℕ) : ℤ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  show (1 : ℝ) / (x - (((k + 1 : ℕ) : ℤ) : ℝ)) ^ 2 = _
  rw [hc]

theorem h3_one_div_add_succ_sq_summable (x : ℝ) :
    Summable (fun n : ℕ =>
      (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  classical
  have hg_sum : Summable (fun n : ℤ => 1 / (x - (n : ℝ)) ^ 2) :=
    one_div_sub_sq_summable x
  have hinj_neg : Function.Injective
      (fun k : ℕ => (-((k + 1 : ℕ) : ℤ) : ℤ)) := by
    intro a b hab
    simp only at hab
    have h1 : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) :=
      neg_injective hab
    have h2 : (a + 1 : ℕ) = (b + 1 : ℕ) := by exact_mod_cast h1
    omega
  have hcompNeg := hg_sum.comp_injective hinj_neg
  refine hcompNeg.congr ?_
  intro k
  have hc : ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
      -(((k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hd : (x - (-(((k + 1 : ℕ) : ℝ)))) ^ 2 =
      (x + ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    have : x - (-(((k + 1 : ℕ) : ℝ))) =
        x + ((k + 1 : ℕ) : ℝ) := by ring
    rw [this]
  show (1 : ℝ) / (x - ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)) ^ 2 = _
  rw [hc, hd]

theorem h3VaalerCore_pos_index_form (x : ℝ) :
    h3VaalerCore x =
      (∑' n : ℕ,
        ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 -
          1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) + 2 / x := by
  classical
  unfold h3VaalerCore
  congr 1
  have hsign_sum :
      Summable (fun n : ℤ =>
        Real.sign ((n : ℝ)) / (x - (n : ℝ)) ^ 2) :=
    beurlingB_nonintegerCore_summable x
  have hsplit :=
    tsum_int_eq_zero_add_tsum_pnat hsign_sum
  rw [tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ =>
          Real.sign (((n : ℤ) : ℝ)) / (x - ((n : ℤ) : ℝ)) ^ 2),
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ =>
          Real.sign (((-((n : ℤ)) : ℤ) : ℝ)) /
            (x - ((-((n : ℤ)) : ℤ) : ℝ)) ^ 2)] at hsplit
  have hzero :
      Real.sign (((0 : ℤ) : ℝ)) / (x - ((0 : ℤ) : ℝ)) ^ 2 = 0 := by simp
  rw [hzero, zero_add] at hsplit
  have hpos_eq : ∀ n : ℕ,
      Real.sign ((((n + 1 : ℕ) : ℤ) : ℝ)) /
            (x - (((n + 1 : ℕ) : ℤ) : ℝ)) ^ 2 =
        (1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    intro n
    have hc : (((n + 1 : ℕ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      have hge : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hcast]
      linarith
    have hsgn1 : Real.sign (((n + 1 : ℕ) : ℝ)) = 1 :=
      Real.sign_of_pos hpos
    rw [hc, hsgn1]
  have hneg_eq : ∀ n : ℕ,
      Real.sign (((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)) /
            (x - ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)) ^ 2 =
        -((1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) := by
    intro n
    have hc : ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ) =
        -(((n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      have hge : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hcast]
      linarith
    have hneg : -(((n + 1 : ℕ) : ℝ)) < 0 := by linarith
    have hsgn : Real.sign (-(((n + 1 : ℕ) : ℝ))) = -1 :=
      Real.sign_of_neg hneg
    have hsq : (x - (-(((n + 1 : ℕ) : ℝ)))) ^ 2 =
        (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      have h1 : x - (-(((n + 1 : ℕ) : ℝ))) =
          x + ((n + 1 : ℕ) : ℝ) := by ring
      rw [h1]
    rw [hc, hsgn, hsq]
    by_cases h0 : (x + ((n + 1 : ℕ) : ℝ)) ^ 2 = 0
    · rw [h0]
      simp
    · field_simp
  rw [show (∑' n : ℕ,
        Real.sign ((((n + 1 : ℕ) : ℤ) : ℝ)) /
          (x - (((n + 1 : ℕ) : ℤ) : ℝ)) ^ 2) =
        ∑' n : ℕ, (1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 from
      tsum_congr hpos_eq,
    show (∑' n : ℕ,
        Real.sign (((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)) /
          (x - ((-(((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)) ^ 2) =
        ∑' n : ℕ, -((1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) from
      tsum_congr hneg_eq] at hsplit
  rw [tsum_neg] at hsplit
  have hcomb :
      (∑' n : ℕ,
        ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 -
          (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) =
        (∑' n : ℕ, (1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2) -
        (∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) :=
    (h3_one_div_sub_succ_sq_summable x).tsum_sub
      (h3_one_div_add_succ_sq_summable x)
  linarith

#print axioms h3VaalerH_neg
#print axioms h3VaalerCore_pos_index_form

theorem h3VaalerH_one_minus_eq_kernel_defect {x : ℝ}
    (hx : ¬ ∃ m : ℤ, x = (m : ℝ)) :
    1 - h3VaalerH x =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        (2 * (∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) +
          1 / x ^ 2 - 2 / x) := by
  classical
  -- (a) Unfold `h3VaalerH` on the non-integer branch.
  have hB : h3VaalerH x =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 * h3VaalerCore x := by
    unfold h3VaalerH; simp [hx]
  rw [hB]
  -- (b) Set abbreviations for the sums.
  set Sminus : ℝ := ∑' n : ℕ, (1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2
  set Splus : ℝ := ∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2
  -- (c) Mittag-Leffler "even part": (Sminus + Splus) + 1/x² = π²/sin²(πx).
  have hML :
      (∑' n : ℕ, ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 +
                    1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) + 1 / x ^ 2 =
        Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2 :=
    mittag_leffler_pos_index_form hx
  -- Rewrite the combined tsum as Sminus + Splus.
  have hML_split :
      (∑' n : ℕ, ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 +
                    1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) = Sminus + Splus :=
    (h3_one_div_sub_succ_sq_summable x).tsum_add
      (h3_one_div_add_succ_sq_summable x)
  rw [hML_split] at hML
  -- (d) Positive-index form of core: core(x) = (Sminus − Splus) + 2/x.
  have hCore : h3VaalerCore x =
      (∑' n : ℕ, ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 -
                    1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) + 2 / x :=
    h3VaalerCore_pos_index_form x
  have hCore_split :
      (∑' n : ℕ, ((1 : ℝ) / (x - ((n + 1 : ℕ) : ℝ)) ^ 2 -
                    1 / (x + ((n + 1 : ℕ) : ℝ)) ^ 2)) = Sminus - Splus :=
    (h3_one_div_sub_succ_sq_summable x).tsum_sub
      (h3_one_div_add_succ_sq_summable x)
  rw [hCore_split] at hCore
  -- (e) sin(πx) ≠ 0 since x ∉ ℤ.
  have hsin_ne : Real.sin (Real.pi * x) ≠ 0 := by
    intro hs
    -- sin(πx) = 0 ⇔ ∃ m : ℤ, πx = m·π ⇔ ∃ m : ℤ, x = m.
    -- We invoke this contrapositively using `Real.sin_eq_zero_iff`.
    have hmul : Real.pi * x = Real.pi * x := rfl
    -- `Real.sin_eq_zero_iff_of_lt_of_lt`? Use the generic form.
    -- `Real.sin_eq_zero_iff`: `sin θ = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = θ`.
    have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [Real.sin_eq_zero_iff] at hs
    obtain ⟨n, hn⟩ := hs
    apply hx
    refine ⟨n, ?_⟩
    -- `n * π = π * x` gives `x = n`.
    have : (n : ℝ) * Real.pi = Real.pi * x := hn
    have h2 : Real.pi * (n : ℝ) = Real.pi * x := by linarith [mul_comm (n : ℝ) Real.pi]
    have h3 := mul_left_cancel₀ hπne h2
    exact h3.symm
  -- (f) Combine.  Compute K · (π²/sin²(πx)) = 1.
  have hsin_sq_ne : Real.sin (Real.pi * x) ^ 2 ≠ 0 := pow_ne_zero _ hsin_ne
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπsq_ne : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ hπne
  have hKone :
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        (Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2) = 1 := by
    rw [div_pow]
    field_simp
  -- Plug in.
  -- We want: 1 - K·core(x) = K · (2 Splus + 1/x² - 2/x).
  -- Use:  1 = K · (Sminus + Splus + 1/x²)  (from hKone and hML).
  --       K · core(x) = K · ((Sminus - Splus) + 2/x).
  -- Subtract: 1 - K·core = K · (Sminus + Splus + 1/x² - (Sminus - Splus) - 2/x)
  --                       = K · (2 Splus + 1/x² - 2/x).
  rw [hCore]
  have hKML : (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
      (Sminus + Splus + 1 / x ^ 2) = 1 := by
    calc (Real.sin (Real.pi * x) / Real.pi) ^ 2 * (Sminus + Splus + 1 / x ^ 2)
        = (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
            (Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2) := by rw [hML]
      _ = 1 := hKone
  -- Now algebraically combine.
  have hmove : (1 : ℝ) -
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 * (Sminus - Splus + 2 / x) =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        (2 * Splus + 1 / x ^ 2 - 2 / x) := by
    nlinarith [hKML, sq_nonneg (Real.sin (Real.pi * x) / Real.pi)]
  exact hmove

/-- The Vaaler-`H` defect series `D(x) := 2 · ∑'_{n : ℕ} 1/(x+(n+1))²
+ 1/x² − 2/x` is nonneg on the positive reals.

This is Vaaler 1985, Lemma 5(iv) — equivalent to the upper bound
`H(x) ≤ 1` on positive non-integer reals, via the identity
`1 − H(x) = (sin πx/π)² · D(x)` (see
`h3VaalerH_one_minus_eq_kernel_defect`).

#### Proof outline (trapezoidal lower bound on the tail series).

Set `g(t) := 1/(x+t) + 1/(2(x+t)²)`.  An elementary algebraic
manipulation (`(2y² + 4y + 1) ≤ 2(y+1)²`) shows that, for every
`y > 0`,

  `g(y) − g(y+1) ≤ 1/(x+y)²`.

Specialising to `y = n+1` (`n : ℕ`) and telescoping with `g(N+1) → 0`,

  `g(1) = ∑'_{n : ℕ} (g(n+1) − g(n+2)) ≤ ∑'_{n : ℕ} 1/(x+(n+1))²`.

Substituting `g(1) = 1/(x+1) + 1/(2(x+1)²)` and computing the
arithmetic combination

  `2·g(1) + 1/x² − 2/x = 1/(x²(x+1)²)`

(common denominator `x²(x+1)²`; numerator collapses to `1`) gives
`D(x) ≥ 1/(x²(x+1)²) > 0`, which is the desired nonnegativity. -/
theorem h3VaalerH_kernel_defect_nonneg {x : ℝ} (hxpos : 0 < x) :
    0 ≤ 2 * (∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) +
        1 / x ^ 2 - 2 / x := by
  classical
  -- Comparison series:  h n := g(n+1) − g(n+2)  where
  --   g(t) := 1/(x+t) + 1/(2(x+t)²).
  -- We will show:
  --   (i)  h n ≥ 0 (positivity of each telescope step).
  --   (ii) HasSum h (g 1)  (telescoping).
  --   (iii) h n ≤ 1/(x+(n+1))²  pointwise (the key algebraic estimate).
  -- Then  g(1) ≤ ∑'_{n : ℕ} 1/(x+(n+1))²,  i.e.
  --       1/(x+1) + 1/(2(x+1)²) ≤ ∑.
  -- Hence  2·∑ + 1/x² − 2/x ≥ 2/(x+1) + 1/(x+1)² + 1/x² − 2/x
  --                         = 1/(x²(x+1)²) ≥ 0.
  set g : ℕ → ℝ := fun k => (1 : ℝ) / (x + (k : ℝ))
                              + 1 / (2 * (x + (k : ℝ)) ^ 2) with hg_def
  -- Positivity of the offset `x + (n+1) > 0` for every `n : ℕ`.
  have hxn_pos : ∀ n : ℕ, 0 < x + ((n + 1 : ℕ) : ℝ) := by
    intro n
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hxn_pos' : ∀ k : ℕ, 0 < x + (k : ℝ) := by
    intro k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  -- Monotonicity of `g`:  g (n+1) ≤ g n  for every `n : ℕ`.
  have hg_step_nonneg : ∀ n : ℕ, 0 ≤ g (n + 1) - g (n + 2) := by
    intro n
    have h1 : 0 < x + ((n + 1 : ℕ) : ℝ) := hxn_pos n
    have h2 : 0 < x + ((n + 2 : ℕ) : ℝ) := by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]; linarith
    have hlt : x + ((n + 1 : ℕ) : ℝ) < x + ((n + 2 : ℕ) : ℝ) := by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]; linarith
    have h1ne : x + ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt h1
    have h2ne : x + ((n + 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt h2
    have hprod_pos : 0 < (x + ((n + 1 : ℕ) : ℝ)) * (x + ((n + 2 : ℕ) : ℝ)) :=
      mul_pos h1 h2
    have h1sq_pos : 0 < (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := pow_pos h1 _
    have h2sq_pos : 0 < (x + ((n + 2 : ℕ) : ℝ)) ^ 2 := pow_pos h2 _
    have hrec_le :
        (1 : ℝ) / (x + ((n + 2 : ℕ) : ℝ)) ≤
          (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le h1 (le_of_lt hlt)
    have hsq_le :
        (x + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ (x + ((n + 2 : ℕ) : ℝ)) ^ 2 := by
      have := sq_le_sq' (a := x + ((n + 1 : ℕ) : ℝ))
                        (b := x + ((n + 2 : ℕ) : ℝ)) (by linarith) (le_of_lt hlt)
      exact this
    have hrec_sq_le :
        (1 : ℝ) / (2 * (x + ((n + 2 : ℕ) : ℝ)) ^ 2) ≤
          (1 : ℝ) / (2 * (x + ((n + 1 : ℕ) : ℝ)) ^ 2) := by
      have h2pos1 : (0 : ℝ) < 2 * (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := by linarith
      have h2pos2 : (0 : ℝ) < 2 * (x + ((n + 2 : ℕ) : ℝ)) ^ 2 := by linarith
      have hmul_le :
          2 * (x + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 2 * (x + ((n + 2 : ℕ) : ℝ)) ^ 2 := by
        linarith
      exact one_div_le_one_div_of_le h2pos1 hmul_le
    -- g (n + 2) ≤ g (n + 1).
    have hcast1 : ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := rfl
    have hcast2 : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    simp only [hg_def]
    linarith
  -- Algebraic step inequality:  g(n+1) - g(n+2) ≤ 1/(x + (n+1))².
  have hg_step_le : ∀ n : ℕ,
      g (n + 1) - g (n + 2) ≤ (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    intro n
    have h1 : 0 < x + ((n + 1 : ℕ) : ℝ) := hxn_pos n
    have h2 : 0 < x + ((n + 2 : ℕ) : ℝ) := by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]; linarith
    set y : ℝ := x + ((n + 1 : ℕ) : ℝ) with hy_def
    have hy_pos : 0 < y := h1
    have hxn2_eq : x + ((n + 2 : ℕ) : ℝ) = y + 1 := by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast, hy_def]; ring
    have hy1_pos : 0 < y + 1 := by linarith
    have hyne : y ≠ 0 := ne_of_gt hy_pos
    have hy1ne : y + 1 ≠ 0 := ne_of_gt hy1_pos
    have hysq_pos : 0 < y ^ 2 := pow_pos hy_pos _
    have hy1sq_pos : 0 < (y + 1) ^ 2 := pow_pos hy1_pos _
    -- Direct algebraic inequality in `y`:
    --   1/y + 1/(2y²) - 1/(y+1) - 1/(2(y+1)²) ≤ 1/y²,
    -- equivalent (multiplying by `2·y²·(y+1)²`) to
    --   2(y+1)² + (y+1)² - 2y²(y+1) - y² ≤ 2(y+1)²,
    -- which simplifies to  (y+1)² - 2y²(y+1) - y² ≤ 0,
    -- i.e.  -(2y³ + y² + 2y + 1) + (y² + 2y + 1) ≤ 0
    --      ⇔ 2y³ + 2y² ≥ 0 (true for y > 0).
    -- We prove this directly via `nlinarith` once we clear denominators.
    have htarget : (1 : ℝ) / y + 1 / (2 * y ^ 2) -
        (1 / (y + 1) + 1 / (2 * (y + 1) ^ 2)) ≤ 1 / y ^ 2 := by
      have hpos1 : (0 : ℝ) < 2 * y ^ 2 := by positivity
      have hpos2 : (0 : ℝ) < 2 * (y + 1) ^ 2 := by positivity
      have hpos3 : (0 : ℝ) < y ^ 2 * (2 * (y + 1) ^ 2) := by positivity
      rw [div_add_div _ _ hyne hpos1.ne',
          div_add_div _ _ hy1ne hpos2.ne',
          div_sub_div _ _ (by positivity : y * (2 * y ^ 2) ≠ 0)
                            (by positivity : (y + 1) * (2 * (y + 1) ^ 2) ≠ 0)]
      -- Now form `A/B ≤ 1/y²`, i.e. `A · y² ≤ B`.
      rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < y ^ 2)]
      nlinarith [sq_nonneg y, sq_nonneg (y + 1),
        hy_pos, hy1_pos, mul_pos hy_pos hy1_pos,
        mul_pos hysq_pos hy1sq_pos,
        mul_pos hy_pos hysq_pos,
        mul_pos hy_pos (mul_pos hy_pos hy_pos)]
    -- Translate `htarget` back to the `g`-form.
    have hg1_eq : g (n + 1) = 1 / y + 1 / (2 * y ^ 2) := by
      show (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) +
            1 / (2 * (x + ((n + 1 : ℕ) : ℝ)) ^ 2) =
          1 / y + 1 / (2 * y ^ 2)
      rw [hy_def]
    have hg2_eq : g (n + 2) = 1 / (y + 1) + 1 / (2 * (y + 1) ^ 2) := by
      show (1 : ℝ) / (x + ((n + 2 : ℕ) : ℝ)) +
            1 / (2 * (x + ((n + 2 : ℕ) : ℝ)) ^ 2) =
          1 / (y + 1) + 1 / (2 * (y + 1) ^ 2)
      rw [hxn2_eq]
    rw [hg1_eq, hg2_eq]
    linarith [htarget]
  -- Step (ii):  HasSum (fun n => g (n+1) - g (n+2)) (g 1).
  -- Use `hasSum_iff_tendsto_nat_of_nonneg` together with the telescoping
  -- identity `∑_{k=0}^{N-1} (g (k+1) - g (k+2)) = g 1 - g (N+1)` and
  -- the limit `g (N+1) → 0`.
  -- Partial-sum telescoping identity.
  have hpartial : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (g (k + 1) - g (k + 2))) = g 1 - g (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  -- `g (N+1) → 0` as `N → ∞`.
  -- We use that the offset `x + (N+1)` tends to +∞ (Archimedean property).
  have hsh : Filter.Tendsto (fun N : ℕ => x + ((N + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    -- (N : ℝ) → ∞ via `tendsto_natCast_atTop_atTop`.
    have h0 : Filter.Tendsto (fun N : ℕ => (N : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    -- `((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1` and the latter still tends to `atTop`.
    have hN1 : Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1)
          Filter.atTop Filter.atTop :=
        h0.atTop_add tendsto_const_nhds
      refine h1.congr ?_
      intro N; push_cast; ring
    -- Adding the constant `x` on the left preserves `atTop → atTop`.
    have hxshift : Filter.Tendsto (fun y : ℝ => x + y)
        Filter.atTop Filter.atTop := by
      have := (Filter.tendsto_id (x := Filter.atTop)).atTop_add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => x) _ _)
      refine this.congr ?_
      intro y; simp [id]; ring
    exact hxshift.comp hN1
  have hinv_y : Filter.Tendsto (fun y : ℝ => (1 : ℝ) / y)
      Filter.atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have htendsto_inv :
      Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (x + ((N + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := hinv_y.comp hsh
  -- Tendsto for the squared term.
  have hsq : Filter.Tendsto (fun N : ℕ => (x + ((N + 1 : ℕ) : ℝ)) ^ 2)
      Filter.atTop Filter.atTop := by
    have hpow : Filter.Tendsto (fun y : ℝ => y ^ 2)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
    exact hpow.comp hsh
  have h2sq : Filter.Tendsto (fun N : ℕ => 2 * (x + ((N + 1 : ℕ) : ℝ)) ^ 2)
      Filter.atTop Filter.atTop := by
    have h2 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) * y)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact h2.comp hsq
  have htendsto_inv_sq :
      Filter.Tendsto (fun N : ℕ => (1 : ℝ) /
        (2 * (x + ((N + 1 : ℕ) : ℝ)) ^ 2)) Filter.atTop (nhds 0) :=
    hinv_y.comp h2sq
  have hg_tendsto : Filter.Tendsto (fun N : ℕ => g (N + 1))
      Filter.atTop (nhds 0) := by
    have hg_eq : ∀ N : ℕ, g (N + 1) = (1 : ℝ) / (x + ((N + 1 : ℕ) : ℝ)) +
        1 / (2 * (x + ((N + 1 : ℕ) : ℝ)) ^ 2) := by
      intro N
      simp [hg_def]
    have hsum := htendsto_inv.add htendsto_inv_sq
    have hzero : (0 : ℝ) + 0 = 0 := by ring
    rw [hzero] at hsum
    refine hsum.congr ?_
    intro N
    rw [hg_eq N]
  -- Partial sums tend to g 1.
  have hpartial_tendsto :
      Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N, (g (k + 1) - g (k + 2)))
        Filter.atTop (nhds (g 1)) := by
    have hcongr :
        (fun N : ℕ => ∑ k ∈ Finset.range N, (g (k + 1) - g (k + 2))) =
        fun N : ℕ => g 1 - g (N + 1) := by
      funext N; exact hpartial N
    rw [hcongr]
    have hsubs : Filter.Tendsto (fun N : ℕ => g 1 - g (N + 1))
        Filter.atTop (nhds (g 1 - 0)) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => g 1) _ _).sub hg_tendsto
    simpa using hsubs
  -- Convert to `HasSum`.
  have hhsum_h : HasSum (fun n : ℕ => g (n + 1) - g (n + 2)) (g 1) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg_step_nonneg]
    exact hpartial_tendsto
  have hsumm_h : Summable (fun n : ℕ => g (n + 1) - g (n + 2)) :=
    hhsum_h.summable
  -- Summability of the target series.
  have hsumm_f :
      Summable (fun n : ℕ => (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) :=
    h3_one_div_add_succ_sq_summable x
  -- The crucial comparison:  g 1 = ∑ h ≤ ∑ f.
  have hg1_le :
      g 1 ≤ ∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have htsum_h : (∑' n : ℕ, (g (n + 1) - g (n + 2))) = g 1 := hhsum_h.tsum_eq
    have hcmp : (∑' n : ℕ, (g (n + 1) - g (n + 2))) ≤
        ∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 :=
      Summable.tsum_le_tsum hg_step_le hsumm_h hsumm_f
    linarith [htsum_h, hcmp]
  -- Final algebraic combination.
  --   D(x) := 2·∑ + 1/x² − 2/x ≥ 2·g(1) + 1/x² − 2/x = 1/(x²(x+1)²) ≥ 0.
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hx1_pos : 0 < x + 1 := by linarith
  have hx1ne : x + 1 ≠ 0 := ne_of_gt hx1_pos
  have hxsq_pos : 0 < x ^ 2 := pow_pos hxpos _
  have hx1sq_pos : 0 < (x + 1) ^ 2 := pow_pos hx1_pos _
  -- g 1 = 1/(x+1) + 1/(2(x+1)²).
  have hg1_eq : g 1 = (1 : ℝ) / (x + 1) + 1 / (2 * (x + 1) ^ 2) := by
    have hcast : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
    simp [hg_def, hcast]
  -- Combine.
  have hsum_lb :
      2 * (∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) ≥ 2 * g 1 := by
    have h2pos : (0 : ℝ) ≤ 2 := by norm_num
    nlinarith [hg1_le]
  -- 2·g(1) + 1/x² − 2/x = 1/(x²(x+1)²).
  -- Direct algebraic check via field_simp / ring.
  have halg : 2 * g 1 + 1 / x ^ 2 - 2 / x = 1 / (x ^ 2 * (x + 1) ^ 2) := by
    rw [hg1_eq]
    field_simp
    ring
  have hpos_target : 0 ≤ (1 : ℝ) / (x ^ 2 * (x + 1) ^ 2) := by
    have : 0 < x ^ 2 * (x + 1) ^ 2 := mul_pos hxsq_pos hx1sq_pos
    positivity
  linarith [hsum_lb, halg, hpos_target]

/-- Vaaler 1985, Lemma 5(iv):  the odd interpolant `H = h3VaalerH` is
bounded above by `1` on positive non-integer reals.

Pointwise consequence of `h3VaalerH_one_minus_eq_kernel_defect` (the
algebraic identity, proof-complete) and `h3VaalerH_kernel_defect_nonneg`
(the residual sub-proof-hole). -/

theorem h3VaalerH_succ_sq_tsum_le_inv {x : ℝ} (hxpos : 0 < x) :
    (∑' n : ℕ, (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 1 / x := by
  classical
  -- Each summand is non-negative.
  have hf_nn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    intro n
    have hxn_pos : 0 < x + ((n + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    positivity
  -- Apply `Real.tsum_le_of_sum_range_le` with bound `1 / x`.
  refine Real.tsum_le_of_sum_range_le hf_nn ?_
  intro N
  -- Telescoping bound on the partial sum.
  -- For each `n`, `1/(x+n+1)² ≤ 1/(x+n) - 1/(x+n+1)` (telescope).
  set u : ℕ → ℝ := fun n => (1 : ℝ) / (x + (n : ℝ)) with hu_def
  -- Pointwise inequality:  `(x+n+1)² ≥ (x+n) · (x+n+1)` since `x+n+1 ≥ x+n`,
  -- so the reciprocals reverse:  `1/(x+n+1)² ≤ 1/((x+n)(x+n+1))`.
  have hxn_pos' : ∀ n : ℕ, 0 < x + (n : ℝ) := by
    intro n
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hxsn_pos : ∀ n : ℕ, 0 < x + ((n + 1 : ℕ) : ℝ) := by
    intro n
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hstep : ∀ n : ℕ,
      (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ u n - u (n + 1) := by
    intro n
    -- `u n - u (n+1) = 1/(x+n) - 1/(x+n+1) = 1/((x+n)(x+n+1))`.
    -- Normalize the (n+1 : ℕ) cast.
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hxn_pos_n : 0 < x + (n : ℝ) := hxn_pos' n
    have hxn_pos_sn : 0 < x + ((n : ℝ) + 1) := by
      have := hxsn_pos n
      rw [hcast] at this
      exact this
    -- LHS: `1/(x + ↑(n+1))² = 1/(x + ↑n + 1)²`.
    rw [hcast]
    -- `u n = 1/(x + n)`, `u (n+1) = 1/(x + ↑(n+1)) = 1/(x + n + 1)`.
    have hu0 : u n = 1 / (x + (n : ℝ)) := rfl
    have hu1 : u (n + 1) = 1 / (x + ((n : ℝ) + 1)) := by
      simp only [hu_def]
      congr 1
      push_cast; ring
    rw [hu0, hu1]
    -- `1/(x+n) - 1/(x+n+1) = 1/((x+n)(x+n+1))`.
    have hprod_pos : (0 : ℝ) < (x + (n : ℝ)) * (x + ((n : ℝ) + 1)) :=
      mul_pos hxn_pos_n hxn_pos_sn
    have hudiff :
        (1 : ℝ) / (x + (n : ℝ)) - 1 / (x + ((n : ℝ) + 1)) =
          (1 : ℝ) / ((x + (n : ℝ)) * (x + ((n : ℝ) + 1))) := by
      rw [div_sub_div _ _ (ne_of_gt hxn_pos_n) (ne_of_gt hxn_pos_sn)]
      rw [div_eq_div_iff (mul_ne_zero (ne_of_gt hxn_pos_n) (ne_of_gt hxn_pos_sn))
        (mul_ne_zero (ne_of_gt hxn_pos_n) (ne_of_gt hxn_pos_sn))]
      ring
    rw [hudiff]
    -- Want:  `1/(x+n+1)² ≤ 1/((x+n)(x+n+1))`.
    -- Equivalent to  `(x+n)(x+n+1) ≤ (x+n+1)²`,
    -- i.e.            `(x+n) ≤ (x+n+1)`.
    have hxn1_sq_pos : (0 : ℝ) < (x + ((n : ℝ) + 1)) ^ 2 := by positivity
    rw [div_le_div_iff₀ hxn1_sq_pos hprod_pos]
    have hkey : (x + (n : ℝ)) * (x + ((n : ℝ) + 1)) ≤ (x + ((n : ℝ) + 1)) ^ 2 := by
      have hle : x + (n : ℝ) ≤ x + ((n : ℝ) + 1) := by linarith
      have hxn1_nn : 0 ≤ x + ((n : ℝ) + 1) := hxn_pos_sn.le
      nlinarith [hle, hxn1_nn]
    linarith
  -- Sum the telescoping bound.
  calc ∑ i ∈ Finset.range N, (1 : ℝ) / (x + ((i + 1 : ℕ) : ℝ)) ^ 2
      ≤ ∑ i ∈ Finset.range N, (u i - u (i + 1)) :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = u 0 - u N := by
        induction N with
        | zero => simp
        | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            ring
    _ ≤ u 0 := by
        have hN_nn : 0 ≤ u N := by
          rw [hu_def]
          have hxN_pos := hxn_pos' N
          positivity
        linarith
    _ = 1 / x := by simp [hu_def]

#print axioms h3VaalerH_one_minus_eq_kernel_defect
#print axioms h3VaalerH_kernel_defect_nonneg
#print axioms h3VaalerH_succ_sq_tsum_le_inv


theorem h3Vaaler_one_sub_H_abs_le_K_of_pos
    {x : ℝ} (hxpos : 0 < x) :
    |1 - h3VaalerH x| ≤ h3VaalerK x := by
  classical
  by_cases hx_int : ∃ m : ℤ, x = (m : ℝ)
  · obtain ⟨m, rfl⟩ := hx_int
    have hmpos : (0 : ℝ) < (m : ℝ) := hxpos
    rw [h3VaalerH_intCast, Real.sign_of_pos hmpos]
    simp [h3VaalerK_nonneg]
  · have hxne : x ≠ 0 := ne_of_gt hxpos
    have hid := h3VaalerH_one_minus_eq_kernel_defect hx_int
    let S : ℝ := ∑' n : ℕ,
      (1 : ℝ) / (x + ((n + 1 : ℕ) : ℝ)) ^ 2
    let D : ℝ := 2 * S + 1 / x ^ 2 - 2 / x
    let Kid : ℝ := (Real.sin (Real.pi * x) / Real.pi) ^ 2
    have hD0 : 0 ≤ D := by
      dsimp [D, S]
      exact h3VaalerH_kernel_defect_nonneg hxpos
    have hSle : S ≤ 1 / x := by
      dsimp [S]
      exact h3VaalerH_succ_sq_tsum_le_inv hxpos
    have hDle : D ≤ (x ^ 2)⁻¹ := by
      have htwice : 2 * S ≤ 2 * (1 / x) :=
        mul_le_mul_of_nonneg_left hSle (by norm_num)
      dsimp [D]
      calc
        2 * S + 1 / x ^ 2 - 2 / x ≤
            2 * (1 / x) + 1 / x ^ 2 - 2 / x := by linarith
        _ = (x ^ 2)⁻¹ := by
          rw [one_div]
          ring
    have hKid0 : 0 ≤ Kid := by
      dsimp [Kid]
      positivity
    have hId : 1 - h3VaalerH x = Kid * D := by
      dsimp [Kid, D, S]
      exact hid
    have hnonneg : 0 ≤ 1 - h3VaalerH x := by
      rw [hId]
      exact mul_nonneg hKid0 hD0
    have hupper : 1 - h3VaalerH x ≤ Kid / x ^ 2 := by
      rw [hId, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hDle hKid0
    have hK : h3VaalerK x = Kid / x ^ 2 := by
      unfold h3VaalerK
      rw [if_neg hxne]
      dsimp [Kid]
      field_simp [hxne, Real.pi_ne_zero]
    rw [abs_of_nonneg hnonneg, hK]
    exact hupper

theorem h3Vaaler_sign_sub_abs_le_K (x : ℝ) :
    |(if 0 < x then (1 : ℝ) else if x < 0 then -1 else 0) -
        h3VaalerH x| ≤ h3VaalerK x := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hypos : 0 < -x := by linarith
    have h := h3Vaaler_one_sub_H_abs_le_K_of_pos hypos
    rw [h3VaalerH_neg, h3VaalerK_neg] at h
    have hxnotpos : ¬ 0 < x := not_lt.mpr hxneg.le
    rw [if_neg hxnotpos, if_pos hxneg]
    calc
      |-1 - h3VaalerH x| = |-(1 + h3VaalerH x)| := by
        congr 1
        ring
      _ = |1 + h3VaalerH x| := abs_neg _
      _ ≤ h3VaalerK x := by simpa using h
  · subst x
    simp [h3VaalerK_zero]
  · have h := h3Vaaler_one_sub_H_abs_le_K_of_pos hxpos
    have hxnotneg : ¬ x < 0 := not_lt.mpr hxpos.le
    simp [hxpos, hxnotneg]
    exact h

#print axioms h3Vaaler_one_sub_H_abs_le_K_of_pos
#print axioms h3Vaaler_sign_sub_abs_le_K

end RML.Fourier.Vaaler.Internal
