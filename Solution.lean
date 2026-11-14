module

public import RML.Fourier.Vaaler.Discrepancy.SignedTorusBox

@[expose] public section

/-!
# Vaaler-ETK proven solution adapter

Same theorem statement as Challenge.lean, but with a fully certified
proof from the verified toolkit. The challenge is NOT imported.
-/

namespace VaalerETKChallenge

open Finset
open RML.Fourier.Vaaler.Positive

/-- Verified solution to the signed-weight ETK challenge. -/
theorem signed_torus_box_discrepancy
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ)
    (J : κ → ℕ) (hJ : ∀ i, 1 ≤ J i)
    (a b : κ → ℝ)
    (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb1 : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≠ b i) :
    |(∑ n ∈ N, w n * ∏ i,
        torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i)| ≤
    ∑ A ∈ (univ : Finset κ).powerset.erase ∅,
      (|(∑ n ∈ N, w n *
        ∏ i ∈ A,
          intervalMain (J i) (a i) (b i) (mainCoeff (J i)) (x n i))| +
        ∑ n ∈ N, |w n| *
          (∏ i ∈ A,
            (1 + intervalError (J i) (a i) (b i)
              (errorCoeff (J i)) (x n i)) - 1)) := by
  exact weighted_torus_box_etk_signed
    N w x J hJ a b ha0 ha1 hb0 hb1 hab

#print axioms signed_torus_box_discrepancy

end VaalerETKChallenge
