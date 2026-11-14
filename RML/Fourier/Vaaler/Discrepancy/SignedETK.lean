module

public import RML.Fourier.Vaaler.Discrepancy.AbstractETK

@[expose] public section

/-!
# Tier 4B (Phase I) — signed-weight abstract ETK and total variation

NEW extension module (VAALER-4B-R0001). It does not modify `AbstractETK.lean`;
the nonnegative theorem `ETKd.etk_abstract` is untouched and is recovered below as a
corollary (`ETKd.etk_abstract_of_signed`).

For ARBITRARY real weights `w` (no sign hypothesis) and any finite coordinate type `κ`:

    |∑ₙ wₙ ∏ᵢ (ℓᵢ + σᵢ(xₙᵢ)) − (∑ₙ wₙ) ∏ᵢ ℓᵢ| ≤
       ∑_{A ⊆ κ, A ≠ ∅} ( |∑ₙ wₙ ∏_{i∈A} Pᵢ(xₙᵢ)|  +  ∑ₙ |wₙ| (∏_{i∈A} (1 + Eᵢ(xₙᵢ)) − 1) ).

The main term keeps the SIGNED weights; every approximation remainder is charged to
`|wₙ|`. The only change from the nonnegative proof is the remainder step, where
`|wₙ (Π σ − Π P)| = |wₙ| |Π σ − Π P|` and the tensor rule is multiplied by `|wₙ| ≥ 0`.
-/

open Finset

namespace ETKd

section Variation

variable {ι : Type*}

/-- Total variation (absolute mass) of a signed finite sample: `V(N,w) = ∑_{n∈N} |wₙ|`. -/
noncomputable def signedWeightVariation (N : Finset ι) (w : ι → ℝ) : ℝ :=
  ∑ n ∈ N, |w n|

theorem signedWeightVariation_def (N : Finset ι) (w : ι → ℝ) :
    signedWeightVariation N w = ∑ n ∈ N, |w n| := rfl

theorem signedWeightVariation_nonneg (N : Finset ι) (w : ι → ℝ) :
    0 ≤ signedWeightVariation N w :=
  sum_nonneg fun n _ => abs_nonneg (w n)

@[simp] theorem signedWeightVariation_empty (w : ι → ℝ) :
    signedWeightVariation (∅ : Finset ι) w = 0 := by
  simp [signedWeightVariation]

/-- For nonnegative weights the total variation is the ordinary total mass. -/
theorem signedWeightVariation_eq_sum_of_nonneg (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n) :
    signedWeightVariation N w = ∑ n ∈ N, w n :=
  sum_congr rfl fun n hn => abs_of_nonneg (hw n hn)

/-- For nonpositive weights the total variation is minus the total mass. -/
theorem signedWeightVariation_eq_neg_sum_of_nonpos (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, w n ≤ 0) :
    signedWeightVariation N w = -∑ n ∈ N, w n := by
  rw [signedWeightVariation, ← sum_neg_distrib]
  exact sum_congr rfl fun n hn => abs_of_nonpos (hw n hn)

/-- `|∑ w| ≤ V(N,w)`; the reverse inequality fails in general (see the example below). -/
theorem abs_sum_le_signedWeightVariation (N : Finset ι) (w : ι → ℝ) :
    |∑ n ∈ N, w n| ≤ signedWeightVariation N w :=
  abs_sum_le_sum_abs _ _

/-- The variation only sees `|w|`: it is invariant under `w ↦ -w`. -/
theorem signedWeightVariation_neg (N : Finset ι) (w : ι → ℝ) :
    signedWeightVariation N (fun n => -w n) = signedWeightVariation N w := by
  simp [signedWeightVariation]

/-- The variation of `|w|` (as a weight) equals the variation of `w`. -/
theorem signedWeightVariation_abs (N : Finset ι) (w : ι → ℝ) :
    signedWeightVariation N (fun n => |w n|) = signedWeightVariation N w := by
  simp [signedWeightVariation]

/-- Total variation vanishes exactly when every weight on the sample vanishes. -/
theorem signedWeightVariation_eq_zero_iff (N : Finset ι) (w : ι → ℝ) :
    signedWeightVariation N w = 0 ↔ ∀ n ∈ N, w n = 0 := by
  rw [signedWeightVariation, sum_eq_zero_iff_of_nonneg fun n _ => abs_nonneg (w n)]
  simp

/-- **Cancellation example.** Two samples with weights `+1, −1`:
the signed total mass is `0` while the total variation is `2`. -/
theorem signedWeightVariation_cancel_example :
    (∑ n ∈ (univ : Finset (Fin 2)), (![1, -1] : Fin 2 → ℝ) n) = 0 ∧
      signedWeightVariation (univ : Finset (Fin 2)) ![1, -1] = 2 := by
  constructor
  · simp [Fin.sum_univ_two]
  · simp [signedWeightVariation, Fin.sum_univ_two]
    norm_num

end Variation

section Majorant

variable {κ : Type*}

/-- A majorant of an absolute value is nonnegative (derived, never assumed). -/
theorem error_nonneg_of_majorant {σ P E : ℝ} (h : |σ - P| ≤ E) : 0 ≤ E :=
  (abs_nonneg _).trans h

/-- The tensor error weight `∏ (1 + Eᵢ) − 1` is nonnegative when every `Eᵢ ≥ 0`. -/
theorem prod_one_add_sub_one_nonneg (s : Finset κ) (E : κ → ℝ)
    (hE : ∀ i ∈ s, 0 ≤ E i) : 0 ≤ ∏ i ∈ s, (1 + E i) - 1 := by
  have : (1 : ℝ) ≤ ∏ i ∈ s, (1 + E i) :=
    one_le_prod₀ fun i hi => le_add_of_nonneg_right (hE i hi)
  linarith

/-- The tensor error weight is nonnegative under the majorant certificate alone. -/
theorem tensor_error_nonneg_of_majorant (s : Finset κ) (σ P E : κ → ℝ)
    (hE : ∀ i ∈ s, |σ i - P i| ≤ E i) : 0 ≤ ∏ i ∈ s, (1 + E i) - 1 :=
  prod_one_add_sub_one_nonneg s E fun i hi => error_nonneg_of_majorant (hE i hi)

/-- Product of lengths in `[0,1]` lies in `[0,1]` (the face length factor). -/
theorem face_length_factor_mem (s : Finset κ) (ℓ : κ → ℝ)
    (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) :
    0 ≤ ∏ i ∈ s, ℓ i ∧ ∏ i ∈ s, ℓ i ≤ 1 :=
  ⟨prod_nonneg fun i _ => hℓ0 i, prod_le_one₀ (fun i _ => hℓ0 i) fun i _ => hℓ1 i⟩

end Majorant

variable {κ : Type*} [DecidableEq κ] [Fintype κ] {ι : Type*}

/-- **Signed-weight abstract weighted d-dimensional ETK.**
No sign hypothesis on `w`. The main summand of each nonempty face `A` uses the signed
weights; the approximation remainder of each face uses `|wₙ|`. -/
theorem etk_signed_abstract (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (ℓ : κ → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (σ P E : κ → ℝ → ℝ) (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
  have hexp : ∀ n, ∏ i, (ℓ i + σ i (x n i)) =
      ∑ A ∈ (univ : Finset κ).powerset, (∏ i ∈ A, σ i (x n i)) * ∏ i ∈ univ \ A, ℓ i :=
    fun n => prod_add_expand ℓ (fun i => σ i (x n i))
  simp_rw [hexp, mul_sum]
  rw [sum_comm, ← add_sum_erase _ _ (empty_mem_powerset _)]
  simp only [prod_empty, one_mul, sdiff_empty]
  rw [← sum_mul, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A _ => ?_)
  have hℓA := face_length_factor_mem (univ \ A) ℓ hℓ0 hℓ1
  have hsplit : ∑ n ∈ N, w n * ((∏ i ∈ A, σ i (x n i)) * ∏ i ∈ univ \ A, ℓ i) =
      (∏ i ∈ univ \ A, ℓ i) * (∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i) +
        ∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))) := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit, abs_mul, abs_of_nonneg hℓA.1]
  -- the only change from the nonnegative proof: charge the remainder to `|w n|`
  have hrem : |∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))| ≤
      ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_prod_sub_prod_le A (fun i => σ i (x n i)) (fun i => P i (x n i))
        (fun i => E i (x n i)) (fun i _ => hσ i _) (fun i _ => hE i _)) (abs_nonneg _)
  calc (∏ i ∈ univ \ A, ℓ i) * |∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i) +
        ∑ n ∈ N, w n * (∏ i ∈ A, σ i (x n i) - ∏ i ∈ A, P i (x n i))|
      ≤ 1 * (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
        apply mul_le_mul hℓA.2 _ (abs_nonneg _) zero_le_one
        exact (abs_add_le _ _).trans (add_le_add_right hrem _)
    _ = _ := one_mul _

omit [DecidableEq κ] [Fintype κ] in
/-- Each face bracket of the signed bound is nonnegative. -/
theorem signed_face_term_nonneg (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (σ P E : κ → ℝ → ℝ) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) (A : Finset κ) :
    0 ≤ |∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
        ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1) :=
  add_nonneg (abs_nonneg _) (sum_nonneg fun n _ => mul_nonneg (abs_nonneg _)
    (tensor_error_nonneg_of_majorant A (fun i => σ i (x n i)) (fun i => P i (x n i))
      (fun i => E i (x n i)) fun i _ => hE i _))

omit [DecidableEq κ] [Fintype κ] in
/-- The remainder sum of each face is bounded by `V(N,w)` times the worst error weight. -/
theorem signed_face_error_le_variation (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (E : κ → ℝ → ℝ) (A : Finset κ) (M : ℝ)
    (hM : ∀ n ∈ N, ∏ i ∈ A, (1 + E i (x n i)) - 1 ≤ M) :
    ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1) ≤ signedWeightVariation N w * M := by
  rw [signedWeightVariation, sum_mul]
  exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hM n hn) (abs_nonneg _)

/-- **Recovery of the existing nonnegative theorem.** Under `w ≥ 0` the signed theorem
gives exactly the statement of `ETKd.etk_abstract` (proved here independently of it). -/
theorem etk_abstract_of_signed (N : Finset ι) (w : ι → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → κ → ℝ) (ℓ : κ → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (σ P E : κ → ℝ → ℝ) (hσ : ∀ i t, |σ i t| ≤ 1) (hE : ∀ i t, |σ i t - P i t| ≤ E i t) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| ≤
      ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
        (|∑ n ∈ N, w n * ∏ i ∈ A, P i (x n i)| +
          ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1)) := by
  have h := etk_signed_abstract N w x ℓ hℓ0 hℓ1 σ P E hσ hE
  have hrw : ∀ A : Finset κ, ∑ n ∈ N, |w n| * (∏ i ∈ A, (1 + E i (x n i)) - 1) =
      ∑ n ∈ N, w n * (∏ i ∈ A, (1 + E i (x n i)) - 1) := fun A =>
    sum_congr rfl fun n hn => by rw [abs_of_nonneg (hw n hn)]
  simpa only [hrw] using h

omit [DecidableEq κ] in
/-- **Dimension zero.** For an empty coordinate type the face family is empty and both
sides vanish; the signed theorem specializes to `0 ≤ 0`. -/
theorem etk_signed_abstract_dim_zero [IsEmpty κ] (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (ℓ : κ → ℝ) (σ : κ → ℝ → ℝ) :
    |∑ n ∈ N, w n * ∏ i, (ℓ i + σ i (x n i)) - (∑ n ∈ N, w n) * ∏ i, ℓ i| = 0 := by
  simp

theorem face_family_empty_of_isEmpty [IsEmpty κ] :
    (univ : Finset κ).powerset.erase ∅ = ∅ := by
  simp [univ_eq_empty]

end ETKd

#print axioms ETKd.signedWeightVariation_cancel_example
#print axioms ETKd.etk_signed_abstract
#print axioms ETKd.etk_abstract_of_signed
#print axioms ETKd.etk_signed_abstract_dim_zero
#print axioms ETKd.signed_face_term_nonneg
#print axioms ETKd.signed_face_error_le_variation
