module

public import RML.Fourier.Vaaler.Discrepancy.Frequency
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite frequency boxes for face products

Each nonempty coordinate face has an exact finite tensor-mode expansion
indexed by the dependent box ∏_{i∈A} {1,...,J_i}.
This is a real tensor-mode formula; reducing every real tensor mode to
signed complex single-frequency exponentials is a further optional API.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- Exact frequency-box expansion of the polynomial associated with any
    finite coordinate face A, at arbitrary coordinate-dependent cutoffs. -/
theorem intervalMain_face_eq_frequency_box
    {κ : Type*} [DecidableEq κ]
    (A : Finset κ) (J : κ → ℕ)
    (a b t : κ → ℝ) :
    (∏ i ∈ A, intervalMain (J i) (a i) (b i)
      (mainCoeff (J i)) (t i)) =
    ∑ p ∈ A.pi (fun i => Finset.Icc 1 (J i)),
      ∏ i ∈ A.attach,
        (intervalFrequencyCoeff (J i.1) (a i.1) (b i.1)
          (p i.1 i.2) * realVaalerMode (p i.1 i.2) (t i.1)).re := by
  classical
  simp_rw [intervalMain_eq_frequency_sum]
  exact Finset.prod_sum A (fun i => Finset.Icc 1 (J i))
    (fun i j => (intervalFrequencyCoeff (J i) (a i) (b i) j *
      realVaalerMode j (t i)).re)

#print axioms intervalMain_face_eq_frequency_box
end RML.Fourier.Vaaler.Positive
