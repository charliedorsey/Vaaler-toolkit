module

public import RML.Fourier.Vaaler.Discrepancy.TorusBox

@[expose] public section

/-!
# Explicit degenerate-arc conventions
The existing directed-arc theorem excludes equal endpoints intentionally.
A user who needs an empty or full circle can choose them as constructors
rather than guessing a meaning for equal real representatives.
-/

namespace RML.Fourier.Vaaler.Positive

/-- Explicit torus arc choice. Equal-start/end directions are not silently
identified with either an empty interval or a full circle. -/
inductive TorusArc where
  | empty
  | full
  | directed (a b : ℝ)
  deriving Inhabited

/-- Literal, endpoint-correct membership indicator for an arc choice. -/
noncomputable def TorusArc.indicator : TorusArc → ℝ → ℝ
  | .empty, _ => 0
  | .full, _ => 1
  | .directed a b, t => torusArcIndicator a b t

/-- Volume of the explicitly chosen arc. -/
noncomputable def TorusArc.length : TorusArc → ℝ
  | .empty => 0
  | .full => 1
  | .directed a b => torusArcLength a b

@[simp] theorem TorusArc.empty_indicator (t : ℝ) :
    TorusArc.indicator .empty t = 0 := rfl

@[simp] theorem TorusArc.full_indicator (t : ℝ) :
    TorusArc.indicator .full t = 1 := rfl

@[simp] theorem TorusArc.empty_length :
    TorusArc.length .empty = 0 := rfl

@[simp] theorem TorusArc.full_length :
    TorusArc.length .full = 1 := rfl

@[simp] theorem TorusArc.directed_indicator (a b t : ℝ) :
    TorusArc.indicator (.directed a b) t =
      torusArcIndicator a b t := rfl

@[simp] theorem TorusArc.directed_length (a b : ℝ) :
    TorusArc.length (.directed a b) = torusArcLength a b := rfl

/-- An empty arc has zero discrepancy for every finite weighted sample. -/
theorem TorusArc.empty_discrepancy
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) :
    (∑ n ∈ N, w n * TorusArc.indicator .empty (x n)) -
      (∑ n ∈ N, w n) * TorusArc.length .empty = 0 := by
  simp

/-- A full arc has zero discrepancy for every finite weighted sample. -/
theorem TorusArc.full_discrepancy
    {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) :
    (∑ n ∈ N, w n * TorusArc.indicator .full (x n)) -
      (∑ n ∈ N, w n) * TorusArc.length .full = 0 := by
  simp

#print axioms TorusArc.empty_discrepancy
#print axioms TorusArc.full_discrepancy
end RML.Fourier.Vaaler.Positive
