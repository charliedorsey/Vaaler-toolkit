module

public import RML.Fourier.Vaaler.Discrepancy.SignedOneDimETK

@[expose] public section

/-!
# Tier 4B (Phase I) — kernel-checked negative controls

NEW extension module (VAALER-4B-R0001). These are FALSE-STATEMENT witnesses: they show
that the signed theorem cannot be "simplified" by charging the error to signed data.

Concrete Vaaler control (`J = 1`, interval `[0, 1/4)`, four samples):
  x = (0, 1/2, 1/4, 3/4),  w = (+1, +1, −1, −1).
Then `∑ w = 0`, `S_w(1) = 1 − 1 − i + i = 0`, yet the signed discrepancy equals `1`.
Hence
* the naive bound `2|∑w|/(J+1) + ∑_j (‖c_j‖+‖e_j‖)‖S_w(j)‖` (zero mode with `|∑ w|`
  instead of `V`, error modes with `S_w` instead of `S_|w|`) is FALSE; and
* the `|w|`-weighted Fejér error is `≥ 1` although every `S_w`-based error proxy is `0`.

Abstract control: with `P ≡ 0`, `E ≡ 1` and weights `(+1, −1)`, the variant of
`etk_signed_abstract` with `wₙ` (instead of `|wₙ|`) in the error is FALSE.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- The control sample locations. -/
noncomputable def ncX : Fin 4 → ℝ := ![0, 1 / 2, 1 / 4, 3 / 4]

/-- The control weights: equal mass `+2` and `−2`, total mass `0`, variation `4`. -/
noncomputable def ncW : Fin 4 → ℝ := ![1, 1, -1, -1]

theorem ncW_sum : (∑ n : Fin 4, ncW n) = 0 := by
  norm_num [ncW, Fin.sum_univ_four]

theorem ncW_variation : ETKd.signedWeightVariation (univ : Finset (Fin 4)) ncW = 4 := by
  norm_num [ETKd.signedWeightVariation, ncW, Fin.sum_univ_four]

/-- `S_w(1) = 0` for the control: `1 + e(1/2) − e(1/4) − e(3/4) = 1 − 1 − i + i`. -/
theorem nc_S_one : weightedExponentialSum (univ : Finset (Fin 4)) ncW ncX (1 : ℤ) = 0 := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [show 2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have h4 : Complex.exp (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((1 / 4 : ℝ) : ℂ))) =
      Complex.I := by
    rw [show 2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((1 / 4 : ℝ) : ℂ)) =
      Real.pi / 2 * Complex.I by push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  have h34 : Complex.exp (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((3 / 4 : ℝ) : ℂ))) =
      -Complex.I := by
    have : 2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) * ((3 / 4 : ℝ) : ℂ)) =
        Real.pi * Complex.I + Real.pi / 2 * Complex.I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]; ring
  simp only [weightedExponentialSum, signedFourierMode, Fin.sum_univ_four, ncW, ncX,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h2, h4, h34]
  simp

/-- The control's indicator sum over `[0,1/4)` is `1` (only the point `0`; `1/4` is excluded
by the half-open right endpoint). -/
theorem nc_indicator_sum :
    (∑ n : Fin 4, ncW n *
      (if (0 : ℝ) ≤ Int.fract (ncX n) ∧ Int.fract (ncX n) < 1 / 4 then (1 : ℝ) else 0)) = 1 := by
  have f0 : Int.fract (0 : ℝ) = 0 := Int.fract_zero
  have f1 : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have f2 : Int.fract (1 / 4 : ℝ) = 1 / 4 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have f3 : Int.fract (3 / 4 : ℝ) = 3 / 4 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  simp only [Fin.sum_univ_four, ncW, ncX, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    f0, f1, f2, f3]
  norm_num

/-- The control's signed discrepancy is exactly `1`. -/
theorem nc_discrepancy :
    |(∑ n : Fin 4, ncW n *
        (if (0 : ℝ) ≤ Int.fract (ncX n) ∧ Int.fract (ncX n) < 1 / 4 then (1 : ℝ) else 0)) -
      (∑ n : Fin 4, ncW n) * ((1 / 4 : ℝ) - 0)| = 1 := by
  rw [nc_indicator_sum, ncW_sum]; norm_num

/-- **Negative control (concrete Vaaler).** The naive signed bound — zero mode charged to
`|∑ w|` and all error modes to `S_w` — is FALSE. -/
theorem naive_signed_oneDim_bound_false :
    ¬ (|(∑ n : Fin 4, ncW n *
        (if (0 : ℝ) ≤ Int.fract (ncX n) ∧ Int.fract (ncX n) < 1 / 4 then (1 : ℝ) else 0)) -
        (∑ n : Fin 4, ncW n) * ((1 / 4 : ℝ) - 0)| ≤
      (2 : ℝ) / ((1 : ℕ) + 1) * |∑ n : Fin 4, ncW n| +
        ∑ j ∈ Finset.Icc 1 1,
          (‖intervalFrequencyCoeff 1 0 (1 / 4) j‖ +
            ‖intervalErrorFrequencyCoeff 1 0 (1 / 4) j‖) *
            ‖weightedExponentialSum (univ : Finset (Fin 4)) ncW ncX (j : ℤ)‖) := by
  rw [nc_discrepancy, ncW_sum]
  simp [nc_S_one]

/-- The true signed bound is consistent on the control (sanity): it holds with `V = 4`. -/
theorem nc_true_signed_bound :
    |(∑ n : Fin 4, ncW n *
        (if (0 : ℝ) ≤ Int.fract (ncX n) ∧ Int.fract (ncX n) < 1 / 4 then (1 : ℝ) else 0)) -
        (∑ n : Fin 4, ncW n) * ((1 / 4 : ℝ) - 0)| ≤
      (2 : ℝ) / ((1 : ℕ) + 1) * 4 +
      ∑ j ∈ Finset.Icc 1 1,
        (‖intervalFrequencyCoeff 1 0 (1 / 4) j‖ *
            ‖weightedExponentialSum (univ : Finset (Fin 4)) ncW ncX (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff 1 0 (1 / 4) j‖ *
            ‖absWeightedExponentialSum (univ : Finset (Fin 4)) ncW ncX (j : ℤ)‖) := by
  have h := signed_oneDim_etk_exponential (univ : Finset (Fin 4)) ncW ncX 1 le_rfl
    0 (1 / 4) le_rfl (by norm_num) (by norm_num)
  rwa [ncW_variation] at h

/-- **Negative control (error side).** On the control the `|w|`-weighted Fejér error is at
least `1`, while every `S_w`-only error proxy (zero mode `2|∑w|/(J+1)`, modes `‖S_w(j)‖`)
vanishes. So `S_w` alone cannot control the `|w|`-weighted error. -/
theorem abs_weighted_error_not_controlled_by_S_w :
    1 ≤ (∑ n : Fin 4, |ncW n| * intervalError 1 0 (1 / 4) (errorCoeff 1) (ncX n)) ∧
      (2 : ℝ) / ((1 : ℕ) + 1) * |∑ n : Fin 4, ncW n| +
        ∑ j ∈ Finset.Icc 1 1, ‖intervalErrorFrequencyCoeff 1 0 (1 / 4) j‖ *
          ‖weightedExponentialSum (univ : Finset (Fin 4)) ncW ncX (j : ℤ)‖ = 0 := by
  refine ⟨?_, by rw [ncW_sum]; simp [nc_S_one]⟩
  have hcert := fun t => explicit_halfOpen_interval_certificate 1 le_rfl 0 (1 / 4)
    le_rfl (by norm_num) (by norm_num) t
  have hsplit := signed_abs_discrepancy_le_main_add_error (univ : Finset (Fin 4)) ncW ncX
    (fun t => if (0 : ℝ) ≤ Int.fract t ∧ Int.fract t < 1 / 4 then (1 : ℝ) else 0)
    ((1 / 4 : ℝ) - 0) (intervalSigma 0 (1 / 4)) (intervalMain 1 0 (1 / 4) (mainCoeff 1))
    (intervalError 1 0 (1 / 4) (errorCoeff 1)) (fun t => (hcert t).1)
    (fun t => (hcert t).2.2.1)
  have hmain := weighted_intervalMain_abs_le_exponential_sums
    (univ : Finset (Fin 4)) ncW ncX 1 0 (1 / 4)
  rw [Finset.Icc_self, Finset.sum_singleton] at hmain
  simp only [Nat.cast_one, nc_S_one, norm_zero, mul_zero] at hmain
  rw [nc_discrepancy] at hsplit
  have h0 : |∑ n ∈ (univ : Finset (Fin 4)), ncW n *
      intervalMain 1 0 (1 / 4) (mainCoeff 1) (ncX n)| = 0 :=
    le_antisymm hmain (abs_nonneg _)
  linarith

end RML.Fourier.Vaaler.Positive

namespace ETKd

open Finset

/-- **Negative control (abstract).** The variant of `etk_signed_abstract` with `wₙ`
(instead of `|wₙ|`) in the error is FALSE, already for one coordinate and two samples.
Witness: weights `(+1, −1)`, points `(1/2, −1/2)`, `ℓ = 1/2`, `σ = clamp to [−1/2,1/2]`,
`P ≡ 0`, `E ≡ 1` (all hypotheses hold globally). LHS `= 1`, naive RHS `= 0`. -/
theorem naive_etk_with_signed_error_false :
    ¬ ∀ (w : Fin 2 → ℝ) (x : Fin 2 → Fin 1 → ℝ) (ℓ : Fin 1 → ℝ),
      (∀ i, 0 ≤ ℓ i) → (∀ i, ℓ i ≤ 1) →
      ∀ (σ P E : Fin 1 → ℝ → ℝ), (∀ i t, |σ i t| ≤ 1) → (∀ i t, |σ i t - P i t| ≤ E i t) →
      |∑ n : Fin 2, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n : Fin 2, w n) * ∏ i, ℓ i| ≤
        ∑ A ∈ (univ : Finset (Fin 1)).powerset.erase ∅,
          (|∑ n : Fin 2, w n * ∏ i ∈ A, P i (x n i)| +
            ∑ n : Fin 2, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
  intro h
  let σ : Fin 1 → ℝ → ℝ := fun _ t => max (-1 / 2) (min (1 / 2) t)
  have hσ : ∀ i t, |σ i t| ≤ 1 := by
    intro i t
    rw [abs_le]
    constructor
    · exact le_trans (by norm_num) (le_max_left _ _)
    · exact max_le (by norm_num) ((min_le_left _ _).trans (by norm_num))
  have hE : ∀ i t, |σ i t - (fun _ _ => (0 : ℝ)) i t| ≤ (fun _ _ => (1 : ℝ)) i t := by
    intro i t
    simpa using hσ i t
  have hc := h ![1, -1] ![![1 / 2], ![-1 / 2]] (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) σ (fun _ _ => 0) (fun _ _ => 1) hσ hE
  have hA : (univ : Finset (Fin 1)).powerset.erase ∅ = {univ} := by decide
  have s1 : σ 0 (1 / 2) = 1 / 2 := by
    simp only [σ]; rw [min_self]; exact max_eq_right (by norm_num)
  have s2 : σ 0 (-1 / 2) = -1 / 2 := by
    simp only [σ]; rw [min_eq_right (by norm_num), max_self]
  rw [hA, sum_singleton] at hc
  simp only [Fin.sum_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, s1, s2] at hc
  norm_num at hc

end ETKd
