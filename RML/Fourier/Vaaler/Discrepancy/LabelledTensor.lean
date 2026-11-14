module

public import RML.Fourier.Vaaler.Discrepancy.SignedScalar

@[expose] public section

/-!
# Finite labelled signed-complex tensor expansion

Each coordinate can carry labels (frequency, sign, coefficient choice)
without assuming the labels' integer frequencies are injective.
This is especially useful for Vaaler main and Fejer error coefficients,
where the zero frequency must be retained explicitly.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- A reusable frequency expansion for ANY dependent finite label sets.
Labels may map to the same integer frequency: no hidden injectivity
assumption is used, and all coefficient multiplicities are retained. -/
theorem weighted_tensor_expansion_labelled
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*}
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : (i : κ) → Finset (α i))
    (freq : (i : κ) → α i → ℤ)
    (coeff : (i : κ) → α i → ℂ) :
    (∑ n ∈ N, (w n : ℂ) *
      ∏ i, ∑ p ∈ C i, coeff i p * signedFourierMode (freq i p) (x n i)) =
    ∑ p ∈ Fintype.piFinset C,
      (∏ i, coeff i (p i)) *
        weightedTensorExponentialSum N w x (fun i => freq i (p i)) := by
  classical
  simp_rw [Finset.prod_univ_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  unfold weightedTensorExponentialSum
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← signedTensorMode_eq_dot]
  unfold signedTensorMode
  rw [Finset.prod_mul_distrib]
  ring

/-- A direct bound by the standard integer-frequency exponential sums,
valid for arbitrary real sample weights in this pure algebraic step. -/
theorem weighted_tensor_norm_le_exponential_sums_labelled
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*}
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : (i : κ) → Finset (α i))
    (freq : (i : κ) → α i → ℤ)
    (coeff : (i : κ) → α i → ℂ) :
    ‖∑ n ∈ N, (w n : ℂ) *
      ∏ i, ∑ p ∈ C i, coeff i p * signedFourierMode (freq i p) (x n i)‖ ≤
    ∑ p ∈ Fintype.piFinset C,
      (∏ i, ‖coeff i (p i)‖) *
        ‖weightedTensorExponentialSum N w x (fun i => freq i (p i))‖ := by
  rw [weighted_tensor_expansion_labelled]
  calc
    ‖∑ p ∈ Fintype.piFinset C,
      (∏ i, coeff i (p i)) *
        weightedTensorExponentialSum N w x (fun i => freq i (p i))‖ ≤
      ∑ p ∈ Fintype.piFinset C,
        ‖(∏ i, coeff i (p i)) *
          weightedTensorExponentialSum N w x (fun i => freq i (p i))‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, norm_prod]

#print axioms weighted_tensor_expansion_labelled
#print axioms weighted_tensor_norm_le_exponential_sums_labelled
end RML.Fourier.Vaaler.Positive
