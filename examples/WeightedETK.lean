module

public import RML.Fourier.Vaaler.Toolkit

@[expose] public section

open RML.Fourier.Vaaler.Positive

/-! Real 1D and 2D consumers of the general-dimensional weighted box theorem.
    The theorem result type is inferred here to prevent notation elaboration
    from changing the exact target statement.
-/

/-- One-dimensional weighted box estimate, at all endpoints. -/
example
    {ι : Type*}
    (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → Fin 1 → ℝ)
    (J : Fin 1 → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : Fin 1 → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i ≤ 1) :=
  exists_weighted_box_etk N w hw x J hJ a b ha hab hb

/-- Two-dimensional weighted box estimate, with independent cutoffs. -/
example
    {ι : Type*}
    (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n)
    (x : ι → Fin 2 → ℝ)
    (J : Fin 2 → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : Fin 2 → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i < b i)
    (hb : ∀ i, b i ≤ 1) :=
  exists_weighted_box_etk N w hw x J hJ a b ha hab hb

private def exampleCutoffs : Fin 2 → ℕ :=
  fun i => if i = 0 then 3 else 7

example : exampleCutoffs 0 = 3 := by decide
example : exampleCutoffs 1 = 7 := by decide
example : ∀ i : Fin 2, 1 ≤ exampleCutoffs i := by
  intro i
  fin_cases i <;> decide
