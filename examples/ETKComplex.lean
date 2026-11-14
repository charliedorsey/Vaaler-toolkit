module

public import RML.Fourier.Vaaler.Discrepancy.ETKComplex

@[expose] public section

open RML.Fourier.Vaaler.Positive
open Finset

/-- Explicit two-dimensional consumer with independent cutoffs and one
wrapped, one nonwrapped torus coordinate. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → Fin 2 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i : Fin 2,
       torusArcIndicator
         (if i = 0 then (3/4 : ℝ) else 1/8)
         (if i = 0 then (1/4 : ℝ) else 7/8)
         (x n i)) -
      (∑ n ∈ N, w n) * ∏ i : Fin 2,
        torusArcLength
          (if i = 0 then (3/4 : ℝ) else 1/8)
          (if i = 0 then (1/4 : ℝ) else 7/8)| ≤
    ∑ A ∈ (Finset.univ : Finset (Fin 2)).powerset.erase ∅,
       (mainFaceComplexBound A N w x
          (fun i => if i = 0 then 3 else 7)
          (fun i => if i = 0 then 3/4 else 1/8)
          (fun i => if i = 0 then 1/4 else 7/8) +
        ‖fejerFaceComplexSum A N w x
          (fun i => if i = 0 then 3 else 7)
          (fun i => if i = 0 then 3/4 else 1/8)
          (fun i => if i = 0 then 1/4 else 7/8)‖) := by
  apply weighted_torus_box_etk_complex N w hw x
    (fun i => if i = 0 then 3 else 7)
    (by intro i; fin_cases i <;> norm_num)
    (fun i => if i = 0 then 3/4 else 1/8)
    (fun i => if i = 0 then 1/4 else 7/8)
  all_goals intro i; fin_cases i <;> norm_num

/-- The arbitrary-dimensional theorem also handles an empty coordinate
type, for which the nonempty-face frequency family is empty. -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → Fin 0 → ℝ) (J : Fin 0 → ℕ)
    (a b : Fin 0 → ℝ) :
    |(∑ n ∈ N, w n * ∏ i : Fin 0,
         torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i : Fin 0,
         torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (Finset.univ : Finset (Fin 0)).powerset.erase ∅,
      (mainFaceComplexBound A N w x J a b +
        ‖fejerFaceComplexSum A N w x J a b‖) := by
  apply weighted_torus_box_etk_complex N w hw x J
  all_goals intro i; exact i.elim0

#check weighted_torus_box_etk_complex
