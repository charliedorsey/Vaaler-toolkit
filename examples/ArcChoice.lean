module

public import RML.Fourier.Vaaler.Discrepancy.ArcChoice

@[expose] public section

open RML.Fourier.Vaaler.Positive

-- Equal endpoint users select .empty or .full explicitly.
example (t : ℝ) : TorusArc.indicator .empty t = 0 := by simp
example (t : ℝ) : TorusArc.indicator .full t = 1 := by simp
example : TorusArc.length .empty = 0 := by simp
example : TorusArc.length .full = 1 := by simp

-- Directed intervals keep their original exact half-open semantics.
example (a b t : ℝ) :
    TorusArc.indicator (.directed a b) t =
      torusArcIndicator a b t := by simp

example {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) :
    (∑ n ∈ N, w n * TorusArc.indicator .empty (x n)) -
      (∑ n ∈ N, w n) * TorusArc.length .empty = 0 :=
  TorusArc.empty_discrepancy N w x

example {ι : Type*} (N : Finset ι) (w : ι → ℝ) (x : ι → ℝ) :
    (∑ n ∈ N, w n * TorusArc.indicator .full (x n)) -
      (∑ n ∈ N, w n) * TorusArc.length .full = 0 :=
  TorusArc.full_discrepancy N w x
