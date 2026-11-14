module

public import Mathlib

@[expose] public section

/-!
NEGATIVE CONTROL, NOT A FORMALIZATION OF VAALER–ETK.
Quillon's independent review demonstrated that the R0023 Comparator accepted
this kind of deliberately false redefinition under the old nine definition holes.
Under R0023a's strict zero-hole config the Comparator must reject it by
constant-body mismatch.
-/

namespace RML.Fourier.Vaaler.Internal
noncomputable def h3VaalerJHat (_J : ℕ) (_n : ℤ) : ℝ := 0
end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Positive
noncomputable def yevorin_vaalerMainCoeff (_J _j : ℕ) : ℂ := 0
noncomputable def yevorin_vaalerErrorCoeff (_J _j : ℕ) : ℂ := 0
noncomputable abbrev mainCoeff (_J _j : ℕ) : ℂ := 0
noncomputable abbrev errorCoeff (_J _j : ℕ) : ℂ := 0
noncomputable def intervalMain (_J : ℕ) (_a _b : ℝ) (_c : ℕ → ℂ) (_t : ℝ) : ℝ := 0
noncomputable def intervalError (_J : ℕ) (_a _b : ℝ) (_e : ℕ → ℂ) (_t : ℝ) : ℝ := 0
noncomputable def torusArcLength (_a _b : ℝ) : ℝ := 1
noncomputable def torusArcIndicator (_a _b _t : ℝ) : ℝ := 1
end RML.Fourier.Vaaler.Positive

namespace VaalerETKChallenge

open Finset
open RML.Fourier.Vaaler.Positive

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
  have h0 : (∑ n ∈ N, w n * ∏ i, torusArcIndicator (a i) (b i) (x n i)) -
      (∑ n ∈ N, w n) * ∏ i, torusArcLength (a i) (b i) = 0 := by
    simp only [torusArcIndicator, torusArcLength, Finset.prod_const_one, mul_one, sub_self]
  rw [h0, abs_zero]
  exact Finset.sum_nonneg fun A _ => add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (by simp [intervalError]))

end VaalerETKChallenge
