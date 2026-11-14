module

public import RML.Fourier.Vaaler.Discrepancy.RealTensorBridge
public import RML.Fourier.Vaaler.Discrepancy.SignedScalar

@[expose] public section

/-!
# Small definitional interfaces for the Vaaler main term on a face.
A face is represented as a coordinate subtype rather than elaborating
a large dependent frequency box in each theorem's result type.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

noncomputable def mainFaceValue
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) : ℝ :=
  ∑ n ∈ N, w n * ∏ i : A,
    intervalMain (J i.1) (a i.1) (b i.1)
      (mainCoeff (J i.1)) (x n i.1)

noncomputable def mainFaceComplexBound
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) : ℝ :=
  ∑ p ∈ Fintype.piFinset (fun i : A => signedPairSupport (J i.1)),
    (∏ i : A, ‖signedMainCoeff (J i.1) (a i.1) (b i.1) (p i)‖) *
    ‖weightedTensorExponentialSum N w
      (fun n (i : A) => x n i.1)
      (fun i : A => signedPairFrequency (p i))‖

/-- The exact weighted real face sum used in the existing ETK theorem. -/
theorem mainFaceValue_eq
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) :
    mainFaceValue A N w x J a b =
      ∑ n ∈ N, w n * ∏ i ∈ A,
        intervalMain (J i) (a i) (b i)
          (mainCoeff (J i)) (x n i) := by
  classical
  unfold mainFaceValue
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact (Finset.prod_coe_sort A
    (fun i : κ => intervalMain (J i) (a i) (b i)
      (mainCoeff (J i)) (x n i)))

/-- The actual Vaaler main term on any face is bounded by classical
finite signed complex frequencies with explicit coefficients. -/
theorem mainFaceValue_abs_le_complexBound
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) :
    |mainFaceValue A N w x J a b| ≤
      mainFaceComplexBound A N w x J a b := by
  classical
  have h := weighted_real_tensor_abs_le_exponential_sums_labelled
    N w (fun n (i : A) => x n i.1)
    (fun (i : A) t => intervalMain (J i.1) (a i.1) (b i.1)
      (mainCoeff (J i.1)) t)
    (fun (i : A) => signedPairSupport (J i.1))
    (fun (i : A) p => signedPairFrequency p)
    (fun (i : A) p => signedMainCoeff (J i.1) (a i.1) (b i.1) p)
    (fun (i : A) t => signedMain_eq_two_sided (J i.1) (a i.1) (b i.1) t)
  exact h

#print axioms mainFaceValue_eq
#print axioms mainFaceValue_abs_le_complexBound
end RML.Fourier.Vaaler.Positive
