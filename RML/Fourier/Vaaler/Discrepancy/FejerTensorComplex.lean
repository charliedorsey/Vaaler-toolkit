module

public import RML.Fourier.Vaaler.Discrepancy.FejerErrorLabels

@[expose] public section

/-!
# Exact explicit signed-complex Fejér tensor-error formula

This is algebraic: no sign assumptions on real weights. It keeps the
subtraction of the bare mass term visible and does not claim a norm
bound before the zero-frequency cancellation has been proved.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- A tensor of the full 1 + E factors is an exact finite sum of
ordinary complex exponential sums with signed integer frequency vectors. -/
theorem weighted_fejer_tensor_eq_signed_box
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (J : κ → ℕ) (a b : κ → ℝ) :
    ((∑ n ∈ N, w n *
      ∏ i, (1 + intervalError (J i) (a i) (b i)
        (errorCoeff (J i)) (x n i)) : ℝ) : ℂ) =
    ∑ p ∈ Fintype.piFinset (fun i => signedErrorOneSupport (J i)),
      (∏ i, signedErrorOneCoeff (J i) (a i) (b i) (p i)) *
        weightedTensorExponentialSum N w x
          (fun i => signedErrorOneFreq (p i)) := by
  classical
  exact weighted_real_tensor_expansion_labelled
    N w x
    (fun i t => 1 + intervalError (J i) (a i) (b i)
      (errorCoeff (J i)) t)
    (fun i => signedErrorOneSupport (J i))
    (fun i p => signedErrorOneFreq p)
    (fun i p => signedErrorOneCoeff (J i) (a i) (b i) p)
    (fun i t => signedErrorOne_eq_two_sided (J i) (a i) (b i) t)

/-- Exact Fejér tensor error: the minus-one is never discarded.
The finite signed-frequency expansion minus the total signed sample mass
is shown before the zero mode is collected. -/
theorem weighted_fejer_tensor_error_eq_signed_box
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (J : κ → ℕ) (a b : κ → ℝ) :
    ((∑ n ∈ N, w n *
      ((∏ i, (1 + intervalError (J i) (a i) (b i)
        (errorCoeff (J i)) (x n i))) - 1) : ℝ) : ℂ) =
    (∑ p ∈ Fintype.piFinset (fun i => signedErrorOneSupport (J i)),
      (∏ i, signedErrorOneCoeff (J i) (a i) (b i) (p i)) *
        weightedTensorExponentialSum N w x
          (fun i => signedErrorOneFreq (p i))) -
      ((∑ n ∈ N, w n : ℝ) : ℂ) := by
  classical
  have h := weighted_fejer_tensor_eq_signed_box N w x J a b
  calc
    _ = ((∑ n ∈ N, w n *
      ∏ i, (1 + intervalError (J i) (a i) (b i)
        (errorCoeff (J i)) (x n i)) : ℝ) : ℂ) -
      ((∑ n ∈ N, w n : ℝ) : ℂ) := by
        push_cast
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
    _ = _ := by rw [h]

#print axioms weighted_fejer_tensor_eq_signed_box
#print axioms weighted_fejer_tensor_error_eq_signed_box

end RML.Fourier.Vaaler.Positive
