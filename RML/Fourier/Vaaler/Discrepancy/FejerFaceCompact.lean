module

public import RML.Fourier.Vaaler.Discrepancy.FejerTensorComplex

@[expose] public section

/-!
# Fejer error over a finite coordinate face in explicit complex modes

Each coordinate face is represented by its finite subtype.
The constant contribution is subtracted EXACTLY, rather than
being silently upper-bounded before zero-mode cancellation.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

noncomputable def fejerFaceValue
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) : ℝ :=
  ∑ n ∈ N, w n *
    ((∏ i : A, (1 + intervalError (J i.1) (a i.1) (b i.1)
      (errorCoeff (J i.1)) (x n i.1))) - 1)

noncomputable def fejerFaceComplexSum
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) : ℂ :=
  (∑ p ∈ Fintype.piFinset (fun i : A => signedErrorOneSupport (J i.1)),
    (∏ i : A, signedErrorOneCoeff (J i.1) (a i.1) (b i.1) (p i)) *
      weightedTensorExponentialSum N w
        (fun n (i : A) => x n i.1)
        (fun i : A => signedErrorOneFreq (p i))) -
    ((∑ n ∈ N, w n : ℝ) : ℂ)

/-- The error face has an exact signed complex-frequency expansion,
including the subtraction of its bare sample mass. -/
theorem fejerFaceValue_eq_signed_box
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) :
    ((fejerFaceValue A N w x J a b : ℝ) : ℂ) =
      fejerFaceComplexSum A N w x J a b := by
  classical
  exact weighted_fejer_tensor_error_eq_signed_box
    N w (fun n (i : A) => x n i.1)
    (fun i : A => J i.1)
    (fun i : A => a i.1)
    (fun i : A => b i.1)

/-- Valid explicit complex-sum upper bound for the weighted error face.
This keeps the zero-frequency subtraction inside the complex norm. -/
theorem fejerFaceValue_le_complex_norm
    {κ ι : Type*} [DecidableEq κ]
    (A : Finset κ) (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (J : κ → ℕ) (a b : κ → ℝ) :
    fejerFaceValue A N w x J a b ≤
      ‖fejerFaceComplexSum A N w x J a b‖ := by
  have h := congrArg Complex.re
    (fejerFaceValue_eq_signed_box A N w x J a b)
  simp only [Complex.ofReal_re] at h
  rw [h]
  exact Complex.re_le_norm _

#print axioms fejerFaceValue_eq_signed_box
#print axioms fejerFaceValue_le_complex_norm
end RML.Fourier.Vaaler.Positive
