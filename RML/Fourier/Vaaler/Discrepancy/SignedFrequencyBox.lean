module

public import RML.Fourier.Vaaler.Discrepancy.SignedTorusBox
public import RML.Fourier.Vaaler.Discrepancy.SignedScalar

@[expose] public section

/-!
# Tier 4B Phase II (OPTIONAL) — flattened signed complex frequency-box form (VAALER-4B-R0002)

NEW extension module, kept separate from the core signed box theorem so it can be accepted or
deferred independently. For every nonempty face `A`:

* the MAIN face `|∑ₙ wₙ ∏_{i∈A} Pᵢ(xₙᵢ)|` is bounded by the SIGNED tensor sums
  `S_w(h) = ∑ₙ wₙ e(⟨h, xₙ⟩)` over an explicit labelled box: coordinates `i ∈ A` carry the
  labels `some (j, ±)` with frequency `±j`, `1 ≤ j ≤ J i`; coordinates `i ∉ A` carry only the
  zero label `none` (frequency 0, coefficient 1);
* the ERROR face `∑ₙ |wₙ| (∏_{i∈A} (1 + Eᵢ(xₙᵢ)) − 1)` is computed EXACTLY in the ABSOLUTE
  tensor sums `S_|w|(h)`: coordinates `i ∈ A` carry `none` with coefficient `1 + 2/(J i + 1)`
  and `some (j, ±)` with `signedErrorCoeff`. The all-zero label contributes
  `∏_{i∈A} (1 + 2/(J i+1)) · V(N,w)`, from which the `−1` term removes exactly `V(N,w)`.
  Hence the face's zero-frequency part is `(∏_{i∈A} (1 + 2/(J i+1)) − 1) · V(N,w)`, never a
  multiple of `|∑ w|`.

Labels are used (rather than integer frequencies) so the finite support is explicit and no
image-injectivity argument is needed. Not claimed: sharp constants; merging equal frequencies.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Frequency of a label: the zero label `none` has frequency 0. -/
def labelFreq : Option (ℕ × Bool) → ℤ
  | none => 0
  | some p => signedPairFrequency p

/-- Generalized (labelled) finite tensor expansion: each coordinate has its own finite label
set, complex coefficients, and integer frequency map. Arbitrary real weights. -/
theorem weighted_tensor_expansion_labelled_uniform
    {κ ι α : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq α]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : κ → Finset α) (c : κ → α → ℂ) (f : κ → α → ℤ) :
    (∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ l ∈ C i, c i l * signedFourierMode (f i l) (x n i)) =
    ∑ l ∈ Fintype.piFinset C,
      (∏ i, c i (l i)) * weightedTensorExponentialSum N w x (fun i => f i (l i)) := by
  simp_rw [Finset.prod_univ_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  unfold weightedTensorExponentialSum
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← signedTensorMode_eq_dot]
  unfold signedTensorMode
  rw [Finset.prod_mul_distrib]
  ring

theorem weighted_tensor_norm_le_labelled
    {κ ι α : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq α]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : κ → Finset α) (c : κ → α → ℂ) (f : κ → α → ℤ) :
    ‖∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ l ∈ C i, c i l * signedFourierMode (f i l) (x n i)‖ ≤
    ∑ l ∈ Fintype.piFinset C,
      (∏ i, ‖c i (l i)‖) * ‖weightedTensorExponentialSum N w x (fun i => f i (l i))‖ := by
  rw [weighted_tensor_expansion_labelled_uniform]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
  rw [norm_mul, norm_prod]

section Faces

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Main-face labels: the signed pair support on `A`, the zero label off `A`. -/
noncomputable def mainFaceLabels (J : κ → ℕ) (A : Finset κ) (i : κ) :
    Finset (Option (ℕ × Bool)) :=
  if i ∈ A then (signedPairSupport (J i)).map Function.Embedding.some else {none}

/-- Main-face label coefficients (`none ↦ 1`, `some p ↦ signedMainCoeff`). -/
noncomputable def mainFaceCoeff (J : κ → ℕ) (a b : κ → ℝ) (i : κ) :
    Option (ℕ × Bool) → ℂ
  | none => 1
  | some p => signedMainCoeff (J i) (a i) (b i) p

/-- Error-face labels: zero label plus signed pair support on `A`, zero label off `A`. -/
noncomputable def errorFaceLabels (J : κ → ℕ) (A : Finset κ) (i : κ) :
    Finset (Option (ℕ × Bool)) :=
  if i ∈ A then insert none ((signedPairSupport (J i)).map Function.Embedding.some) else {none}

/-- Error-face label coefficients. On `A` the zero label carries `1 + 2/(J i + 1)`
(the factor `1 + Eᵢ` has zero mode `1 + 2/(J i + 1)`); off `A` it carries `1`. -/
noncomputable def errorFaceCoeff (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) (i : κ) :
    Option (ℕ × Bool) → ℂ
  | none => if i ∈ A then 1 + 2 / ((J i : ℂ) + 1) else 1
  | some p => signedErrorCoeff (J i) (a i) (b i) p

/-- The all-zero label. -/
def zeroLabel : κ → Option (ℕ × Bool) := fun _ => none

theorem signedFourierMode_zero (t : ℝ) : signedFourierMode 0 t = 1 := by
  simp [signedFourierMode]

omit [Fintype κ] in
theorem mainFace_coord (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) (i : κ) (t : ℝ) :
    (if i ∈ A then ((intervalMain (J i) (a i) (b i) (mainCoeff (J i)) t : ℝ) : ℂ) else 1) =
      ∑ l ∈ mainFaceLabels J A i, mainFaceCoeff J a b i l * signedFourierMode (labelFreq l) t := by
  by_cases hi : i ∈ A
  · simp only [hi, ite_true, mainFaceLabels, Finset.sum_map, Function.Embedding.some_apply,
      mainFaceCoeff, labelFreq]
    exact signedMain_eq_two_sided (J i) (a i) (b i) t
  · simp [hi, mainFaceLabels, mainFaceCoeff, labelFreq, signedFourierMode_zero]

omit [Fintype κ] in
theorem errorFace_coord (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) (i : κ) (t : ℝ) :
    (if i ∈ A then ((1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) t : ℝ) : ℂ)
      else 1) =
      ∑ l ∈ errorFaceLabels J A i,
        errorFaceCoeff J a b A i l * signedFourierMode (labelFreq l) t := by
  by_cases hi : i ∈ A
  · have hnone : (none : Option (ℕ × Bool)) ∉
        (signedPairSupport (J i)).map Function.Embedding.some := by simp
    simp only [hi, ite_true, errorFaceLabels]
    rw [Finset.sum_insert hnone, Finset.sum_map]
    simp only [errorFaceCoeff, hi, ite_true, labelFreq, signedFourierMode_zero, mul_one,
      Function.Embedding.some_apply]
    push_cast
    rw [signedError_eq_two_sided]
    ring
  · simp [hi, errorFaceLabels, errorFaceCoeff, labelFreq, signedFourierMode_zero]

theorem zeroLabel_mem_errorFaceLabels (J : κ → ℕ) (A : Finset κ) :
    (zeroLabel : κ → Option (ℕ × Bool)) ∈ Fintype.piFinset (errorFaceLabels J A) := by
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hi : i ∈ A <;> simp [zeroLabel, errorFaceLabels, hi]

omit [DecidableEq κ] in
/-- `S_|w|(0) = V(N,w)`. -/
theorem absTensorSum_zero {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ) :
    weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (zeroLabel i)) =
      (ETKd.signedWeightVariation N w : ℂ) := by
  simp [weightedTensorExponentialSum, signedTensorDotMode, zeroLabel, labelFreq,
    ETKd.signedWeightVariation]

/-- Every signed-pair label has a nonzero integer frequency (`±j`, `1 ≤ j`). -/
theorem signedPairFrequency_ne_zero {J : ℕ} {p : ℕ × Bool} (hp : p ∈ signedPairSupport J) :
    signedPairFrequency p ≠ 0 := by
  change p ∈ (Finset.Icc 1 J) ×ˢ (Finset.univ : Finset Bool) at hp
  have h1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
  unfold signedPairFrequency
  split_ifs <;> omega

omit [Fintype κ] in
/-- On a nonempty face, every main label has a NONZERO frequency vector: the main faces carry
no zero mode. -/
theorem mainFace_freq_ne_zero (J : κ → ℕ) (A : Finset κ) (hA : A.Nonempty)
    [Fintype κ] (l : κ → Option (ℕ × Bool)) (hl : l ∈ Fintype.piFinset (mainFaceLabels J A)) :
    (fun i => labelFreq (l i)) ≠ 0 := by
  obtain ⟨i, hi⟩ := hA
  have hmi := Fintype.mem_piFinset.mp hl i
  simp only [mainFaceLabels, hi, ite_true, Finset.mem_map, Function.Embedding.some_apply] at hmi
  obtain ⟨p, hp, hpl⟩ := hmi
  intro h0
  have := congrFun h0 i
  simp only [← hpl, labelFreq, Pi.zero_apply] at this
  exact signedPairFrequency_ne_zero hp this

omit [Fintype κ] in
/-- Every error label other than the all-zero label has a NONZERO frequency vector: the
error face's zero mode is exactly the explicit `(∏(1 + 2/(J i+1)) − 1)·V` term. -/
theorem errorFace_freq_ne_zero (J : κ → ℕ) (A : Finset κ) [Fintype κ]
    (l : κ → Option (ℕ × Bool))
    (hl : l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel) :
    (fun i => labelFreq (l i)) ≠ 0 := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hl
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hmi := Fintype.mem_piFinset.mp hmem i
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hi
  rw [hp] at hmi
  by_cases hiA : i ∈ A
  · simp only [errorFaceLabels, hiA, ite_true, Finset.mem_insert, reduceCtorEq,
      Finset.mem_map, Function.Embedding.some_apply, Option.some.injEq, false_or] at hmi
    obtain ⟨q, hq, rfl⟩ := hmi
    intro h0
    have := congrFun h0 i
    simp only [hp, labelFreq, Pi.zero_apply] at this
    exact signedPairFrequency_ne_zero hq this
  · simp [errorFaceLabels, hiA] at hmi

variable {ι : Type*}

/-- **Main face, flattened.** Signed weights, explicit labelled support. -/
theorem signed_main_face_le_frequency_box
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) :
    |∑ n ∈ N, w n * ∏ i ∈ A, intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i)| ≤
      ∑ l ∈ Fintype.piFinset (mainFaceLabels J A),
        (∏ i, ‖mainFaceCoeff J a b i (l i)‖) *
          ‖weightedTensorExponentialSum N w x (fun i => labelFreq (l i))‖ := by
  have hcast : ((∑ n ∈ N, w n *
      ∏ i ∈ A, intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i) : ℝ) : ℂ) =
      ∑ n ∈ N, (w n : ℂ) * ∏ i, ∑ l ∈ mainFaceLabels J A i,
        mainFaceCoeff J a b i l * signedFourierMode (labelFreq l) (x n i) := by
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [← Fintype.prod_ite_mem A]
    exact Finset.prod_congr rfl fun i _ => mainFace_coord J a b A i (x n i)
  have h := weighted_tensor_norm_le_labelled N w x (mainFaceLabels J A) (mainFaceCoeff J a b)
    (fun _ => labelFreq)
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Error face, exact identity.** Absolute weights, explicit labelled support, the all-zero
label included; the `−1` of the face removes exactly `V(N,w)`. -/
theorem abs_error_face_eq_frequency_box
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) :
    ((∑ n ∈ N, |w n| *
      (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1) : ℝ) : ℂ) =
      (∑ l ∈ Fintype.piFinset (errorFaceLabels J A),
        (∏ i, errorFaceCoeff J a b A i (l i)) *
          weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (l i))) -
        (ETKd.signedWeightVariation N w : ℂ) := by
  rw [← weighted_tensor_expansion_labelled_uniform N (fun n => |w n|) x (errorFaceLabels J A)
    (errorFaceCoeff J a b A) (fun _ => labelFreq)]
  have hprod : ∀ n, (∏ i, ∑ l ∈ errorFaceLabels J A i,
      errorFaceCoeff J a b A i l * signedFourierMode (labelFreq l) (x n i)) =
      ((∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) : ℝ) : ℂ) := by
    intro n
    push_cast
    rw [← Fintype.prod_ite_mem A]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← errorFace_coord J a b A i (x n i)]
    push_cast
    rfl
  simp_rw [hprod]
  simp only [ETKd.signedWeightVariation]
  push_cast
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Error face, bound.** Zero-frequency part `(∏_{i∈A}(1 + 2/(J i+1)) − 1)·V(N,w)`;
every other label is charged to `‖S_|w|‖`. -/
theorem abs_error_face_le_frequency_box
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) (A : Finset κ) :
    (∑ n ∈ N, |w n| *
      (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1)) ≤
      (∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1)) - 1) * ETKd.signedWeightVariation N w +
      ∑ l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel,
        (∏ i, ‖errorFaceCoeff J a b A i (l i)‖) *
          ‖weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (l i))‖ := by
  set r : ℝ := ∑ n ∈ N, |w n| *
      (∏ i ∈ A, (1 + intervalError (J i) (a i) (b i) (errorCoeff (J i)) (x n i)) - 1) with hr
  set T : (κ → Option (ℕ × Bool)) → ℂ := fun l => (∏ i, errorFaceCoeff J a b A i (l i)) *
      weightedTensorExponentialSum N (fun n => |w n|) x (fun i => labelFreq (l i)) with hT
  have hid := abs_error_face_eq_frequency_box N w x J a b A
  rw [← add_sum_erase _ _ (zeroLabel_mem_errorFaceLabels J A)] at hid
  have hzero : T zeroLabel =
      (((∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1))) * ETKd.signedWeightVariation N w : ℝ) : ℂ) := by
    simp only [hT, absTensorSum_zero]
    push_cast
    congr 1
    rw [← Fintype.prod_ite_mem A]
    exact Finset.prod_congr rfl fun i _ => by
      by_cases hi : i ∈ A <;> simp [zeroLabel, errorFaceCoeff, hi]
  have hsplit : (r : ℂ) =
      (((∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1)) - 1) * ETKd.signedWeightVariation N w : ℝ) : ℂ) +
        ∑ l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel, T l := by
    rw [hid]
    change T zeroLabel + _ - _ = _
    rw [hzero]
    push_cast
    ring
  have hre : r = ((∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1)) - 1) * ETKd.signedWeightVariation N w) +
      (∑ l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel, T l).re := by
    have := congrArg Complex.re hsplit
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re] at this
    exact this
  rw [hre]
  refine add_le_add le_rfl ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_))
  exact le_of_eq (Finset.sum_congr rfl fun l _ => by rw [hT]; simp only [norm_mul, norm_prod])

end Faces

/-- **Flattened signed torus-box ETK (optional interface).** Arbitrary finite dimension,
arbitrary real weights, independent cutoffs, mixed wrapped/unwrapped arcs. Main faces use the
signed tensor sums `S_w`; error faces use `S_|w|` and the total variation `V`. -/
theorem signed_torus_box_etk_frequency
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i) (a b : κ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) (hab : ∀ i, a i ≠ b i) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      ((∑ l ∈ Fintype.piFinset (mainFaceLabels J A),
          (∏ i, ‖mainFaceCoeff J a b i (l i)‖) *
            ‖weightedTensorExponentialSum N w x (fun i => labelFreq (l i))‖) +
        ((∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1)) - 1) * ETKd.signedWeightVariation N w +
          ∑ l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel,
            (∏ i, ‖errorFaceCoeff J a b A i (l i)‖) *
              ‖weightedTensorExponentialSum N (fun n => |w n|) x
                (fun i => labelFreq (l i))‖)) :=
  (weighted_torus_box_etk_signed N w x J hJ a b ha0 ha1 hb0 hb1 hab).trans
    (Finset.sum_le_sum fun A _ => add_le_add
      (signed_main_face_le_frequency_box N w x J a b A)
      (abs_error_face_le_frequency_box N w x J a b A))

/-- **External-bound consumer (optional interface).** Supply independent bounds
`‖S_w(h)‖ ≤ B h`, `‖S_|w|(h)‖ ≤ C h` and `V(N,w) ≤ Vbar`. -/
theorem signed_torus_box_etk_external_bounds
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i) (a b : κ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) (hab : ∀ i, a i ≠ b i)
    (B C : (κ → ℤ) → ℝ) (Vbar : ℝ)
    (hB : ∀ h, ‖weightedTensorExponentialSum N w x h‖ ≤ B h)
    (hC : ∀ h, ‖weightedTensorExponentialSum N (fun n => |w n|) x h‖ ≤ C h)
    (hV : ETKd.signedWeightVariation N w ≤ Vbar) :
    |(∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      ((∑ l ∈ Fintype.piFinset (mainFaceLabels J A),
          (∏ i, ‖mainFaceCoeff J a b i (l i)‖) * B (fun i => labelFreq (l i))) +
        ((∏ i ∈ A, (1 + (2 : ℝ) / (J i + 1)) - 1) * Vbar +
          ∑ l ∈ (Fintype.piFinset (errorFaceLabels J A)).erase zeroLabel,
            (∏ i, ‖errorFaceCoeff J a b A i (l i)‖) * C (fun i => labelFreq (l i)))) := by
  refine (signed_torus_box_etk_frequency N w x J hJ a b ha0 ha1 hb0 hb1 hab).trans
    (Finset.sum_le_sum fun A _ => add_le_add
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hB _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _))
      (add_le_add (mul_le_mul_of_nonneg_left hV ?_)
        (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hC _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _))))
  exact ETKd.prod_one_add_sub_one_nonneg A (fun i => (2 : ℝ) / (J i + 1))
    (fun i _ => by positivity)

#print axioms weighted_tensor_expansion_labelled_uniform
#print axioms weighted_tensor_norm_le_labelled
#print axioms mainFace_coord
#print axioms errorFace_coord
#print axioms absTensorSum_zero
#print axioms signed_main_face_le_frequency_box
#print axioms abs_error_face_eq_frequency_box
#print axioms abs_error_face_le_frequency_box
#print axioms signed_torus_box_etk_frequency
#print axioms mainFace_freq_ne_zero
#print axioms errorFace_freq_ne_zero
#print axioms signed_torus_box_etk_external_bounds

end RML.Fourier.Vaaler.Positive
