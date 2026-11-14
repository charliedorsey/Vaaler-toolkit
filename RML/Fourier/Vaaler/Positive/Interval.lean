module

public import RML.Fourier.Vaaler.Positive.Core

@[expose] public section

/-! A literal half-open interval certificate, including both jump endpoints. -/
namespace RML.Fourier.Vaaler.Positive

private theorem fract_sub_eq_self_if
    (x y : ℝ) (hx : x < 1) (hy : 0 ≤ y) (hxy : y ≤ x) :
    Int.fract (x - y) = x - y :=
  Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

private theorem fract_sub_eq_one_if
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    Int.fract (x - y) = x - y + 1 := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith, by linarith, ?_⟩
  refine ⟨(-1 : ℤ), ?_⟩
  push_cast
  ring

/-- Exact identity for the left-closed/right-open arc, including integer
    translates and the cases a=0 or b=1. -/
theorem halfOpen_indicator_eq_saw
    (a b t : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (if a ≤ Int.fract t ∧ Int.fract t < b then (1 : ℝ) else 0) =
      (b - a) + saw (t - b) - saw (t - a) := by
  let x := Int.fract t
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  have hbx : 0 ≤ b := le_trans ha hab.le
  have hfa : Int.fract (t - a) = Int.fract (x - a) := by
    simpa [x] using (Int.fract_fract_sub t a).symm
  have hfb : Int.fract (t - b) = Int.fract (x - b) := by
    simpa [x] using (Int.fract_fract_sub t b).symm
  simp only [saw]
  rw [hfa, hfb]
  change (if a ≤ x ∧ x < b then (1 : ℝ) else 0) = _
  by_cases hxa : x < a
  · have hxb : x < b := lt_trans hxa hab
    have h1 := fract_sub_eq_one_if x a hx0 (le_trans hab.le hb) hxa
    have h2 := fract_sub_eq_one_if x b hx0 hb hxb
    have hn : ¬ (a ≤ x ∧ x < b) := by intro h; exact (not_le.mpr hxa) h.1
    simp [hn, h1, h2]
    ring
  · have hax : a ≤ x := le_of_not_gt hxa
    by_cases hxb : x < b
    · have h1 := fract_sub_eq_self_if x a hx1 ha hax
      have h2 := fract_sub_eq_one_if x b hx0 hb hxb
      simp [hax, hxb, h1, h2]
      ring
    · have hbx : b ≤ x := le_of_not_gt hxb
      have h1 := fract_sub_eq_self_if x a hx1 ha (le_trans hab.le hbx)
      have h2 := fract_sub_eq_self_if x b hx1 (le_trans ha hab.le) hbx
      have hn : ¬ (a ≤ x ∧ x < b) := by intro h; exact (not_lt.mpr hbx) h.2
      simp [hn, h1, h2]
      ring

#print axioms halfOpen_indicator_eq_saw
end RML.Fourier.Vaaler.Positive
