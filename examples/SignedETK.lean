module

public import RML.Fourier.Vaaler.Discrepancy.SignedNegativeControl

@[expose] public section

/-!
# Tier 4B Phase I consumers (VAALER-4B-R0001)

Checked with `lake env lean examples/SignedETK.lean`. Every `example` is a real proof.
-/

open Finset RML.Fourier.Vaaler.Positive

/-! ## Total variation API -/

example : ETKd.signedWeightVariation (∅ : Finset ℕ) (fun n => (n : ℝ) - 3) = 0 := by simp

example {ι : Type*} (N : Finset ι) (w : ι → ℝ) : 0 ≤ ETKd.signedWeightVariation N w :=
  ETKd.signedWeightVariation_nonneg N w

-- all-positive: V = ∑ w
example : ETKd.signedWeightVariation (univ : Finset (Fin 3)) ![1, 2, 3] = 6 := by
  rw [ETKd.signedWeightVariation_eq_sum_of_nonneg _ _ (by intro n _; fin_cases n <;> norm_num)]
  simp [Fin.sum_univ_three]; norm_num

-- all-negative: V = -∑ w
example : ETKd.signedWeightVariation (univ : Finset (Fin 2)) ![-1, -5] = 6 := by
  rw [ETKd.signedWeightVariation_eq_neg_sum_of_nonpos _ _ (by intro n _; fin_cases n <;> norm_num)]
  simp [Fin.sum_univ_two]; norm_num

-- zero weights: V = 0
example : ETKd.signedWeightVariation (univ : Finset (Fin 5)) (fun _ => (0 : ℝ)) = 0 := by
  simp [ETKd.signedWeightVariation]

-- cancellation: ∑ w = 0 while V = 2 > 0
example : (∑ n : Fin 2, (![1, -1] : Fin 2 → ℝ) n) = 0 ∧
    0 < ETKd.signedWeightVariation (univ : Finset (Fin 2)) ![1, -1] := by
  obtain ⟨h1, h2⟩ := ETKd.signedWeightVariation_cancel_example
  exact ⟨h1, by rw [h2]; norm_num⟩

/-! ## Abstract signed ETK in dimensions 0, 1, 2, 4 (arbitrary packages, signed weights) -/

-- dimension 0: empty face family, both sides vanish
example {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → Fin 0 → ℝ) (ℓ : Fin 0 → ℝ)
    (σ : Fin 0 → ℝ → ℝ) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| = 0 :=
  ETKd.etk_signed_abstract_dim_zero N w x ℓ σ

example : (univ : Finset (Fin 0)).powerset.erase ∅ = ∅ := ETKd.face_family_empty_of_isEmpty

section Abstract
variable {ι : Type*} (N : Finset ι) (w : ι → ℝ)

example (x : ι → Fin 1 → ℝ) (ℓ : Fin 1 → ℝ)
    (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) (σ P E : Fin 1 → ℝ → ℝ)
    (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset (Fin 1)).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1)) :=
  ETKd.etk_signed_abstract N w x ℓ hℓ0 hℓ1 σ P E hσ hE

example (x : ι → Fin 2 → ℝ) (ℓ : Fin 2 → ℝ)
    (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) (σ P E : Fin 2 → ℝ → ℝ)
    (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1)) :=
  ETKd.etk_signed_abstract N w x ℓ hℓ0 hℓ1 σ P E hσ hE

-- 3 = 2^2 - 1 nonempty faces in dimension 2; 1 in dimension 1
example : ((univ : Finset (Fin 2)).powerset.erase ∅).card = 3 := by decide
example : ((univ : Finset (Fin 1)).powerset.erase ∅).card = 1 := by decide

-- Fin 4 with four genuinely different packages (one per coordinate) and signed weights
example (x : ι → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (σ P E : Fin 4 → ℝ → ℝ) (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset (Fin 4)).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1)) :=
  ETKd.etk_signed_abstract N w x ℓ hℓ0 hℓ1 σ P E hσ hE

-- 15 = 2^4 - 1 nonempty faces in dimension 4
example : ((univ : Finset (Fin 4)).powerset.erase ∅).card = 15 := by decide

-- existing nonnegative theorem recovered under hw (statement identical to etk_abstract)
example (hw : ∀ n ∈ N, 0 ≤ w n) (x : ι → Fin 2 → ℝ) (ℓ : Fin 2 → ℝ)
    (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) (σ P E : Fin 2 → ℝ → ℝ)
    (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1)) :=
  ETKd.etk_abstract_of_signed N w hw x ℓ hℓ0 hℓ1 σ P E hσ hE

-- empty sample: the signed bound holds with LHS = 0
example (x : ι → Fin 2 → ℝ) (ℓ : Fin 2 → ℝ) (σ : Fin 2 → ℝ → ℝ) :
    |∑ n ∈ (∅ : Finset ι), w n * ∏ i, (ℓ i + σ i (x n i)) -
      (∑ n ∈ (∅ : Finset ι), w n) * ∏ i, ℓ i| = 0 := by simp

end Abstract

/-! ## Signed 1D ETK with the named Vaaler coefficients -/

section OneDim
variable {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ)

-- nonwrapped [0, 1/2), J = 3, arbitrary signed weights
example :
    |(∑ n ∈ N, w n *
        (if (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1 / 2 then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * ((1 / 2 : ℝ) - 0)| ≤
      (2 : ℝ) / ((3 : ℕ) + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 3,
        (‖intervalFrequencyCoeff 3 0 (1 / 2) j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff 3 0 (1 / 2) j‖ *
            ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_etk_exponential N w x 3 (by norm_num) 0 (1 / 2) le_rfl (by norm_num)
    (by norm_num)

-- wrapped arc [3/4, 1) ∪ [0, 1/4), J = 7
example :
    |(∑ n ∈ N, w n * torusArcIndicator (3 / 4) (1 / 4) (x n)) -
      (∑ n ∈ N, w n) * torusArcLength (3 / 4) (1 / 4)| ≤
      (2 : ℝ) / ((7 : ℕ) + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 7,
        (‖intervalFrequencyCoeff 7 (3 / 4) (1 / 4) j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff 7 (3 / 4) (1 / 4) j‖ *
            ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_arc_etk_exponential N w x 7 (by norm_num) (3 / 4) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- the wrapped arc has length 1/2
example : torusArcLength (3 / 4) (1 / 4) = 1 / 2 := by
  simp only [torusArcLength]; norm_num

-- full representative [0,1): indicator 1, length 1, J = 2
example : |(∑ n ∈ N, w n * torusArcIndicator 0 1 (x n)) -
      (∑ n ∈ N, w n) * torusArcLength 0 1| ≤
      (2 : ℝ) / ((2 : ℕ) + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 2,
        (‖intervalFrequencyCoeff 2 0 1 j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff 2 0 1 j‖ * ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_arc_etk_exponential N w x 2 (by norm_num) 0 1
    le_rfl zero_le_one zero_le_one le_rfl zero_ne_one

example (t : ℝ) : torusArcIndicator 0 1 t = 1 ∧ torusArcLength 0 1 = 1 := by
  refine ⟨?_, by simp [torusArcLength]⟩
  simp [torusArcIndicator, Int.fract_nonneg, Int.fract_lt_one]

-- empty representative [1,0): indicator 0, length 0, J = 5
example (t : ℝ) : torusArcIndicator 1 0 t = 0 ∧ torusArcLength 1 0 = 0 := by
  refine ⟨?_, by simp [torusArcLength]⟩
  have h1 := Int.fract_lt_one t
  have h0 := Int.fract_nonneg t
  norm_num [torusArcIndicator, not_le.mpr h1, not_lt.mpr h0]

example : |(∑ n ∈ N, w n * torusArcIndicator 1 0 (x n)) -
      (∑ n ∈ N, w n) * torusArcLength 1 0| ≤
      (2 : ℝ) / ((5 : ℕ) + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 5,
        (‖intervalFrequencyCoeff 5 1 0 j‖ * ‖weightedExponentialSum N w x (j : ℤ)‖ +
          ‖intervalErrorFrequencyCoeff 5 1 0 j‖ * ‖absWeightedExponentialSum N w x (j : ℤ)‖) :=
  signed_oneDim_arc_etk_exponential N w x 5 (by norm_num) 1 0
    zero_le_one le_rfl le_rfl zero_le_one one_ne_zero

-- exact half-open endpoints: left endpoint included, right endpoint excluded
example : torusArcIndicator (1 / 4) (1 / 2) (1 / 4) = 1 ∧
    torusArcIndicator (1 / 4) (1 / 2) (1 / 2) = 0 := by
  have f1 : Int.fract (1 / 4 : ℝ) = 1 / 4 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have f2 : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  simp only [torusArcIndicator, f1, f2]; norm_num

-- integer translation invariance of the arc indicator
example (a b t : ℝ) (k : ℤ) : torusArcIndicator a b (t + k) = torusArcIndicator a b t := by
  simp [torusArcIndicator, Int.fract_add_intCast]

-- external-bound consumer: independently supplied bounds for S_w, S_|w| and V
example (Vbar : ℝ) (hV : ETKd.signedWeightVariation N w ≤ Vbar) (B C : ℕ → ℝ)
    (hB : ∀ j ∈ Finset.Icc (1 : ℕ) 3, ‖weightedExponentialSum N w x (j : ℤ)‖ ≤ B j)
    (hC : ∀ j ∈ Finset.Icc (1 : ℕ) 3, ‖absWeightedExponentialSum N w x (j : ℤ)‖ ≤ C j) :
    |(∑ n ∈ N, w n * torusArcIndicator (3 / 4) (1 / 4) (x n)) -
      (∑ n ∈ N, w n) * torusArcLength (3 / 4) (1 / 4)| ≤
      (2 : ℝ) / ((3 : ℕ) + 1) * Vbar +
      ∑ j ∈ Finset.Icc (1 : ℕ) 3,
        (‖intervalFrequencyCoeff 3 (3 / 4) (1 / 4) j‖ * B j +
          ‖intervalErrorFrequencyCoeff 3 (3 / 4) (1 / 4) j‖ * C j) :=
  signed_oneDim_arc_etk_external_bounds N w x 3 (by norm_num) (3 / 4) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Vbar hV B C hB hC

-- the error's zero mode is exactly 2 V/(J+1): exact identity
example (J : ℕ) (a b : ℝ) :
    (∑ n ∈ N, |w n| * intervalError J a b (errorCoeff J) (x n)) =
    (2 : ℝ) / (J + 1) * ETKd.signedWeightVariation N w +
      ∑ j ∈ Finset.Icc 1 J,
        (intervalErrorFrequencyCoeff J a b j * absWeightedExponentialSum N w x (j : ℤ)).re :=
  signed_intervalError_eq_exponential_sums N w x J a b

-- recovery of the existing nonnegative 1D theorem
example (hw : ∀ n ∈ N, 0 ≤ w n) :
    |(∑ n ∈ N, w n *
        (if (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1 / 2 then (1 : ℝ) else 0)) -
      (∑ n ∈ N, w n) * ((1 / 2 : ℝ) - 0)| ≤
      (2 : ℝ) / ((3 : ℕ) + 1) * (∑ n ∈ N, w n) +
      ∑ j ∈ Finset.Icc 1 3,
        (‖intervalFrequencyCoeff 3 0 (1 / 2) j‖ + ‖intervalErrorFrequencyCoeff 3 0 (1 / 2) j‖) *
          ‖weightedExponentialSum N w x (j : ℤ)‖ :=
  weighted_oneDim_etk_exponential_of_signed N w hw x 3 (by norm_num) 0 (1 / 2) le_rfl
    (by norm_num) (by norm_num)

end OneDim

-- equal-location canceling weights: the signed discrepancy is 0 (variation 2)
example (t : ℝ) :
    |(∑ n : Fin 2, (![1, -1] : Fin 2 → ℝ) n * torusArcIndicator (3 / 4) (1 / 4) ((fun _ => t) n)) -
      (∑ n : Fin 2, (![1, -1] : Fin 2 → ℝ) n) * torusArcLength (3 / 4) (1 / 4)| = 0 := by
  simp [Fin.sum_univ_two]

/-! ## Negative controls (false statements, kernel-checked) -/

#check @naive_signed_oneDim_bound_false
#check @abs_weighted_error_not_controlled_by_S_w
#check @nc_true_signed_bound
#check @ETKd.naive_etk_with_signed_error_false
#print axioms naive_signed_oneDim_bound_false
#print axioms abs_weighted_error_not_controlled_by_S_w
#print axioms ETKd.naive_etk_with_signed_error_false
