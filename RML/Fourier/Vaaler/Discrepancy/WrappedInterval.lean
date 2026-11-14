module

public import RML.Fourier.Vaaler.Discrepancy.LocalInterval

@[expose] public section

/-!
# Wrapped half-open torus intervals
For 0 ≤ b < a ≤ 1, the arc [a,1) ∪ [0,b) has length 1+b−a
and exactly the same centered sawtooth difference as an ordinary arc.
All jump points, including the integer grid, are covered literally.
-/

namespace RML.Fourier.Vaaler.Positive

theorem wrapped_indicator_eq_saw (a b t : ℝ)
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ 1) :
    (if a ≤ Int.fract t ∨ Int.fract t < b then (1 : ℝ) else 0) =
      (1 + b - a) + intervalSigma a b t := by
  have hordinary := halfOpen_indicator_eq_saw b a t hb hba ha
  let x := Int.fract t
  have hcomplement :
      (if a ≤ x ∨ x < b then (1 : ℝ) else 0) =
        1 - (if b ≤ x ∧ x < a then (1 : ℝ) else 0) := by
    by_cases h : b ≤ x ∧ x < a
    · have hn : ¬(a ≤ x ∨ x < b) := by
        intro h'
        rcases h' with h' | h'
        · exact (not_le.mpr h.2) h'
        · exact (not_lt.mpr h.1) h'
      simp [h, hn]
    · have hp : a ≤ x ∨ x < b := by
        by_contra h'
        push_neg at h'
        exact h ⟨h'.2, h'.1⟩
      simp [h, hp]
  change (if a ≤ x ∨ x < b then (1 : ℝ) else 0) = _
  rw [hcomplement, hordinary]
  dsimp [intervalSigma]
  ring

theorem exists_wrapped_interval_certificate
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ 1) :
    ∃ c e : ℕ → ℂ,
      (∀ j ∈ Finset.Icc 1 J,
        ‖c j‖ ≤ (2 : ℝ) / j ∧ ‖e j‖ ≤ (2 : ℝ) / (J + 1)) ∧
      (∀ t : ℝ,
        (if a ≤ Int.fract t ∨ Int.fract t < b then (1 : ℝ) else 0) =
          (1 + b - a) + intervalSigma a b t ∧
        |intervalSigma a b t| ≤ 1 ∧
        |intervalSigma a b t - intervalMain J a b c t| ≤
          intervalError J a b e t ∧
        0 ≤ intervalError J a b e t) := by
  obtain ⟨c, e, hc, hpoint⟩ :=
    exists_halfOpen_interval_certificate J hJ b a hb hba ha
  refine ⟨c, e, hc, ?_⟩
  intro t
  have hsigma : intervalSigma a b t = -intervalSigma b a t := by
    unfold intervalSigma
    ring
  have hmain : intervalMain J a b c t = -intervalMain J b a c t := by
    unfold intervalMain
    ring
  have herror : intervalError J a b e t = intervalError J b a e t := by
    unfold intervalError
    ring
  refine ⟨wrapped_indicator_eq_saw a b t hb hba ha, ?_, ?_, ?_⟩
  · exact abs_intervalSigma_le_one a b t
  · rw [hsigma, hmain, herror]
    simpa only [neg_sub_neg, abs_sub_comm] using ((hpoint t).2.2.1)
  · rw [herror]
    exact ((hpoint t).2.2.2)

#print axioms wrapped_indicator_eq_saw
#print axioms exists_wrapped_interval_certificate

end RML.Fourier.Vaaler.Positive
