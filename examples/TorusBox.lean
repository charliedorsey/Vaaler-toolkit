module

public import RML.Fourier.Vaaler.Discrepancy.TorusBox
public import RML.Fourier.Vaaler.Discrepancy.ExplicitWeightedETK
public import RML.Fourier.Vaaler.Discrepancy.FrequencyBox

@[expose] public section

/-!
# Real consumers: unequal cutoffs and mixed wrapped coordinates
All demonstrations use the concrete coefficient APIs, without inventing
additional axioms or importing the historical Paper B tree.
-/

open RML.Fourier.Vaaler.Positive

private def demoCutoffs : Fin 2 → ℕ :=
  fun i => if i = 0 then 3 else 7

private noncomputable def demoStarts : Fin 2 → ℝ :=
  fun i => if i = 0 then 3 / 4 else 1 / 4

private noncomputable def demoFinishes : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 / 4 else 3 / 4

private theorem demoCutoffs_positive : ∀ i : Fin 2, 1 ≤ demoCutoffs i := by
  intro i
  fin_cases i <;> decide

private theorem demoStarts_nonneg : ∀ i : Fin 2, 0 ≤ demoStarts i := by
  intro i
  fin_cases i <;> norm_num [demoStarts]

private theorem demoStarts_le_one : ∀ i : Fin 2, demoStarts i ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [demoStarts]

private theorem demoFinishes_nonneg : ∀ i : Fin 2, 0 ≤ demoFinishes i := by
  intro i
  fin_cases i <;> norm_num [demoFinishes]

private theorem demoFinishes_le_one : ∀ i : Fin 2, demoFinishes i ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [demoFinishes]

private theorem demoStarts_ne_finishes : ∀ i : Fin 2,
    demoStarts i ≠ demoFinishes i := by
  intro i
  fin_cases i <;> norm_num [demoStarts, demoFinishes]

example : demoCutoffs 0 = 3 := by decide
example : demoCutoffs 1 = 7 := by decide

/-- The first interval wraps, and the second is an ordinary half-open arc. -/
example : torusArcLength (demoStarts 0) (demoFinishes 0) = 1 / 2 := by
  norm_num [torusArcLength, demoStarts, demoFinishes]

example : torusArcLength (demoStarts 1) (demoFinishes 1) = 1 / 2 := by
  norm_num [torusArcLength, demoStarts, demoFinishes]

/-- Concrete two-dimensional mixed-wrap ETK consumer with J=(3,7). -/
example {ι : Type*} (N : Finset ι) (w : ι → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n) (x : ι → Fin 2 → ℝ) :=
  weighted_torus_box_etk N w hw x demoCutoffs demoCutoffs_positive
    demoStarts demoFinishes demoStarts_nonneg demoStarts_le_one
    demoFinishes_nonneg demoFinishes_le_one demoStarts_ne_finishes

-- Arbitrary-dimensional finite frequency-box expansion remains available.
#check intervalMain_face_eq_frequency_box
#check weighted_box_etk_explicit
#check weighted_torus_box_etk
