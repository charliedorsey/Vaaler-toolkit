module

public import RML.Fourier.Vaaler.Discrepancy.LabelledTensor

@[expose] public section

/-!
# Real tensor products as explicit complex-frequency exponential sums
This is the bridge from a labelled complex polynomial to the norm of
a weighted real tensor, with no dimension or sign restrictions.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- If each real coordinate factor admits a finite labelled complex
frequency expansion, the weighted product is exactly a sum of the
standard complex exponential sums on the entire frequency box. -/
theorem weighted_real_tensor_expansion_labelled
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*}
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (f : κ → ℝ → ℝ)
    (C : (i : κ) → Finset (α i))
    (freq : (i : κ) → α i → ℤ)
    (coeff : (i : κ) → α i → ℂ)
    (hf : ∀ i t, ((f i t : ℝ) : ℂ) =
      ∑ p ∈ C i, coeff i p * signedFourierMode (freq i p) t) :
    ((∑ n ∈ N, w n * ∏ i, f i (x n i) : ℝ) : ℂ) =
      ∑ p ∈ Fintype.piFinset C,
        (∏ i, coeff i (p i)) *
          weightedTensorExponentialSum N w x (fun i => freq i (p i)) := by
  rw [← weighted_tensor_expansion_labelled N w x C freq coeff]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.ofReal_mul, Complex.ofReal_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hf i (x n i)

/-- A norm bound for the weighted real tensor in ordinary signed
complex frequencies. Independent coordinate support sets are allowed. -/
theorem weighted_real_tensor_abs_le_exponential_sums_labelled
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*}
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (f : κ → ℝ → ℝ)
    (C : (i : κ) → Finset (α i))
    (freq : (i : κ) → α i → ℤ)
    (coeff : (i : κ) → α i → ℂ)
    (hf : ∀ i t, ((f i t : ℝ) : ℂ) =
      ∑ p ∈ C i, coeff i p * signedFourierMode (freq i p) t) :
    |∑ n ∈ N, w n * ∏ i, f i (x n i)| ≤
      ∑ p ∈ Fintype.piFinset C,
        (∏ i, ‖coeff i (p i)‖) *
          ‖weightedTensorExponentialSum N w x (fun i => freq i (p i))‖ := by
  have h := weighted_real_tensor_expansion_labelled
    N w x f C freq coeff hf
  have hn := weighted_tensor_norm_le_exponential_sums_labelled
    N w x C freq coeff
  rw [weighted_tensor_expansion_labelled N w x C freq coeff] at hn
  rw [← h] at hn
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hn

#print axioms weighted_real_tensor_expansion_labelled
#print axioms weighted_real_tensor_abs_le_exponential_sums_labelled
end RML.Fourier.Vaaler.Positive
