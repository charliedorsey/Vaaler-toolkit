module

public import Mathlib

@[expose] public section

open Finset
namespace RML.Fourier.Vaaler.Positive

theorem yevorin_sum_Icc_one_eq_range {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, f j) =
      (∑ k ∈ Finset.range J, f (k + 1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

#print axioms yevorin_sum_Icc_one_eq_range
end RML.Fourier.Vaaler.Positive
