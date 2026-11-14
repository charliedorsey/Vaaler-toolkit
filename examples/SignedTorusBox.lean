module

public import RML.Fourier.Vaaler.Discrepancy.SignedFrequencyBox

@[expose] public section

/-!
# Tier 4B Phase II consumers (VAALER-4B-R0002)

Checked with `lake env lean examples/SignedTorusBox.lean`. Signed weights throughout; no sign
hypothesis appears in any signed example.
-/

open Finset RML.Fourier.Vaaler.Positive

section Generic
variable {ι : Type*} (N : Finset ι) (w : ι → ℝ)

/-! ## Fin 2, J = (3, 7): ordinary `[0, 1/2)` × wrapped `[3/4, 1) ∪ [0, 1/4)` -/

example (x : ι → Fin 2 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
      (|(∑ n ∈ N, w n * ∏ i ∈ A,
          intervalMain (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (mainCoeff (![3, 7] i)) (x n i))| +
        ∑ n ∈ N, |w n| * (∏ i ∈ A,
          (1 + intervalError (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (errorCoeff (![3, 7] i)) (x n i)) - 1)) :=
  weighted_torus_box_etk_signed N w x ![3, 7] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4] ![1 / 2, 1 / 4]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)

-- the box volume is (1/2)·(1/2)
example : ∏ i : Fin 2, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) = 1 / 4 := by
  simp [Fin.prod_univ_two, torusArcLength]; norm_num

/-! ## Fin 4, J = (3, 7, 2, 5): ordinary, wrapped, ordinary, wrapped -/

example (x : ι → Fin 4 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i,
        torusArcIndicator (![0, 3 / 4, 1 / 4, 9 / 10] i) (![1 / 2, 1 / 4, 1, 1 / 10] i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i,
        torusArcLength (![0, 3 / 4, 1 / 4, 9 / 10] i) (![1 / 2, 1 / 4, 1, 1 / 10] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 4)).powerset.erase ∅,
      (|(∑ n ∈ N, w n * ∏ i ∈ A,
          intervalMain (![3, 7, 2, 5] i) (![0, 3 / 4, 1 / 4, 9 / 10] i)
            (![1 / 2, 1 / 4, 1, 1 / 10] i) (mainCoeff (![3, 7, 2, 5] i)) (x n i))| +
        ∑ n ∈ N, |w n| * (∏ i ∈ A,
          (1 + intervalError (![3, 7, 2, 5] i) (![0, 3 / 4, 1 / 4, 9 / 10] i)
            (![1 / 2, 1 / 4, 1, 1 / 10] i) (errorCoeff (![3, 7, 2, 5] i)) (x n i)) - 1)) :=
  weighted_torus_box_etk_signed N w x ![3, 7, 2, 5] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4, 1 / 4, 9 / 10] ![1 / 2, 1 / 4, 1, 1 / 10]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)

-- the Fin 4 box volume: (1/2)(1/2)(3/4)(1/5)
example : ∏ i : Fin 4,
    torusArcLength (![0, 3 / 4, 1 / 4, 9 / 10] i) (![1 / 2, 1 / 4, 1, 1 / 10] i) = 3 / 80 := by
  simp [Fin.prod_univ_four, torusArcLength]; norm_num

/-! ## Fin 0: empty face family, both sides vanish -/

example (x : ι → Fin 0 → ℝ) (a b : Fin 0 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| = 0 := by simp

-- the signed theorem itself applies in dimension 0 (all coordinate hypotheses are vacuous)
example (x : ι → Fin 0 → ℝ) (J : Fin 0 → ℕ) (a b : Fin 0 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (univ : Finset (Fin 0)).powerset.erase ∅,
      (|(∑ n ∈ N, w n * ∏ i ∈ A, intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, |w n| *
          (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1)) :=
  weighted_torus_box_etk_signed N w x J (fun i => i.elim0) a b (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)

/-! ## Recovery of the unchanged nonnegative theorem under `w ≥ 0` (Fin 2, J = (3,7)) -/

example (hw : ∀ n ∈ N, 0 ≤ w n) (x : ι → Fin 2 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
      (|(∑ n ∈ N, w n * ∏ i ∈ A,
          intervalMain (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (mainCoeff (![3, 7] i)) (x n i))| +
        ∑ n ∈ N, w n * (∏ i ∈ A,
          (1 + intervalError (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (errorCoeff (![3, 7] i)) (x n i)) - 1)) :=
  weighted_torus_box_etk_of_signed N w hw x ![3, 7] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4] ![1 / 2, 1 / 4]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)

/-! ## Optional flattened interface: Fin 2, J = (3,7), mixed arcs -/

example (x : ι → Fin 2 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
      ((∑ l ∈ Fintype.piFinset (mainFaceLabels ![3, 7] A),
          (∏ i, ‖mainFaceCoeff ![3, 7] ![0, 3 / 4] ![1 / 2, 1 / 4] i (l i)‖) *
            ‖weightedTensorExponentialSum N w x (fun i => labelFreq (l i))‖) +
        ((∏ i ∈ A, (1 + (2 : ℝ) / ((![3, 7] : Fin 2 → ℕ) i + 1)) - 1) *
            ETKd.signedWeightVariation N w +
          ∑ l ∈ (Fintype.piFinset (errorFaceLabels ![3, 7] A)).erase zeroLabel,
            (∏ i, ‖errorFaceCoeff ![3, 7] ![0, 3 / 4] ![1 / 2, 1 / 4] A i (l i)‖) *
              ‖weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (l i))‖)) :=
  signed_torus_box_etk_frequency N w x ![3, 7] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4] ![1 / 2, 1 / 4]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)

-- external-bound consumer, Fin 4, J = (3,7,2,5)
example (x : ι → Fin 4 → ℝ) (B C : (Fin 4 → ℤ) → ℝ) (Vbar : ℝ)
    (hB : ∀ h, ‖weightedTensorExponentialSum N w x h‖ ≤ B h)
    (hC : ∀ h, ‖weightedTensorExponentialSum N (fun n => |w n|) x h‖ ≤ C h)
    (hV : ETKd.signedWeightVariation N w ≤ Vbar) :
    |(∑ n ∈ N, w n * ∏ i,
        torusArcIndicator (![0, 3 / 4, 1 / 4, 9 / 10] i) (![1 / 2, 1 / 4, 1, 1 / 10] i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i,
        torusArcLength (![0, 3 / 4, 1 / 4, 9 / 10] i) (![1 / 2, 1 / 4, 1, 1 / 10] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 4)).powerset.erase ∅,
      ((∑ l ∈ Fintype.piFinset (mainFaceLabels ![3, 7, 2, 5] A),
          (∏ i, ‖mainFaceCoeff ![3, 7, 2, 5] ![0, 3 / 4, 1 / 4, 9 / 10]
            ![1 / 2, 1 / 4, 1, 1 / 10] i (l i)‖) * B (fun i => labelFreq (l i))) +
        ((∏ i ∈ A, (1 + (2 : ℝ) / ((![3, 7, 2, 5] : Fin 4 → ℕ) i + 1)) - 1) * Vbar +
          ∑ l ∈ (Fintype.piFinset (errorFaceLabels ![3, 7, 2, 5] A)).erase zeroLabel,
            (∏ i, ‖errorFaceCoeff ![3, 7, 2, 5] ![0, 3 / 4, 1 / 4, 9 / 10]
              ![1 / 2, 1 / 4, 1, 1 / 10] A i (l i)‖) * C (fun i => labelFreq (l i)))) :=
  signed_torus_box_etk_external_bounds N w x ![3, 7, 2, 5] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4, 1 / 4, 9 / 10] ![1 / 2, 1 / 4, 1, 1 / 10]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) B C Vbar hB hC hV

-- exact error-face identity (zero label included, the `-1` removes exactly V)
example (x : ι → Fin 2 → ℝ) (A : Finset (Fin 2)) :
    ((∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + intervalError (![3, 7] i) (![0, 3 / 4] i)
        (![1 / 2, 1 / 4] i) (errorCoeff (![3, 7] i)) (x n i)) - 1) : ℝ) : ℂ) =
      (∑ l ∈ Fintype.piFinset (errorFaceLabels ![3, 7] A),
        (∏ i, errorFaceCoeff ![3, 7] ![0, 3 / 4] ![1 / 2, 1 / 4] A i (l i)) *
          weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (l i))) -
        (ETKd.signedWeightVariation N w : ℂ) :=
  abs_error_face_eq_frequency_box N w x ![3, 7] ![0, 3 / 4] ![1 / 2, 1 / 4] A

end Generic

/-! ## Explicit supports: zero and both ± frequencies -/

example : labelFreq none = 0 := rfl
example : labelFreq (some (3, true)) = 3 := rfl
example : labelFreq (some (3, false)) = -3 := rfl
example : (signedPairSupport 3).card = 6 := by
  simp [signedPairSupport, Finset.card_product]
-- off the face only the zero label; on the face the zero label carries 1 + 2/(J+1)
example : mainFaceLabels ![3, 7] {0} 1 = {none} := by simp [mainFaceLabels]
example : errorFaceCoeff ![3, 7] ![0, 3 / 4] ![1 / 2, 1 / 4] {0, 1} 1 none =
    1 + 2 / ((7 : ℂ) + 1) := by
  simp [errorFaceCoeff]
example : none ∈ errorFaceLabels ![3, 7] {0} 0 := by simp [errorFaceLabels]
example : none ∉ mainFaceLabels ![3, 7] {0} 0 := by simp [mainFaceLabels]

-- no hidden zero modes: on a nonempty face every main label, and every error label other
-- than the all-zero one, has a nonzero frequency vector
example (A : Finset (Fin 4)) (hA : A.Nonempty) (l : Fin 4 → Option (ℕ × Bool))
    (hl : l ∈ Fintype.piFinset (mainFaceLabels ![3, 7, 2, 5] A)) :
    (fun i => labelFreq (l i)) ≠ 0 :=
  mainFace_freq_ne_zero ![3, 7, 2, 5] A hA l hl

example (A : Finset (Fin 4)) (l : Fin 4 → Option (ℕ × Bool))
    (hl : l ∈ (Fintype.piFinset (errorFaceLabels ![3, 7, 2, 5] A)).erase zeroLabel) :
    (fun i => labelFreq (l i)) ≠ 0 :=
  errorFace_freq_ne_zero ![3, 7, 2, 5] A l hl

/-! ## Concrete signed samples in Fin 2 -/

-- equal-location canceling weights: signed discrepancy 0, variation 2
example (p : Fin 2 → ℝ) :
    |(∑ n : Fin 2, (![1, -1] : Fin 2 → ℝ) n *
        ∏ i, torusArcIndicator (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) ((fun _ => p) n i)) -
      (∑ n : Fin 2, (![1, -1] : Fin 2 → ℝ) n) *
        ∏ i, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)| = 0 := by
  simp [Fin.sum_univ_two]

-- all-negative weights: the signed theorem applies with no extra hypothesis
example (x : Fin 3 → Fin 2 → ℝ) :
    |(∑ n : Fin 3, (![-1, -2, -3] : Fin 3 → ℝ) n *
        ∏ i, torusArcIndicator (![0, 3 / 4] i) (![1 / 2, 1 / 4] i) (x n i)) -
      (∑ n : Fin 3, (![-1, -2, -3] : Fin 3 → ℝ) n) *
        ∏ i, torusArcLength (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)| ≤
    ∑ A ∈ (univ : Finset (Fin 2)).powerset.erase ∅,
      (|(∑ n : Fin 3, (![-1, -2, -3] : Fin 3 → ℝ) n * ∏ i ∈ A,
          intervalMain (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (mainCoeff (![3, 7] i)) (x n i))| +
        ∑ n : Fin 3, |(![-1, -2, -3] : Fin 3 → ℝ) n| * (∏ i ∈ A,
          (1 + intervalError (![3, 7] i) (![0, 3 / 4] i) (![1 / 2, 1 / 4] i)
            (errorCoeff (![3, 7] i)) (x n i)) - 1)) :=
  weighted_torus_box_etk_signed univ ![-1, -2, -3] x ![3, 7] (by intro i; fin_cases i <;> decide)
    ![0, 3 / 4] ![1 / 2, 1 / 4]
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)

#print axioms weighted_torus_box_etk_signed
#print axioms weighted_torus_box_etk_of_signed
#print axioms signed_torus_box_etk_frequency
#print axioms signed_torus_box_etk_external_bounds
