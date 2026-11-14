module

public import RML.Fourier.Vaaler.Positive
public import RML.Fourier.Vaaler.Positive.Interval

@[expose] public section

namespace RML.Fourier.Vaaler.Positive

open Finset

noncomputable def approxMain (J : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, (c j * realVaalerMode j t).re

noncomputable def approxError (J : ℕ) (e : ℕ → ℂ) (t : ℝ) : ℝ :=
  (1 : ℝ) / (J + 1) +
    ∑ j ∈ Finset.Icc 1 J, (e j * realVaalerMode j t).re

noncomputable def intervalSigma (a b t : ℝ) : ℝ :=
  saw (t - b) - saw (t - a)

noncomputable def intervalMain (J : ℕ) (a b : ℝ)
    (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  approxMain J c (t - b) - approxMain J c (t - a)

noncomputable def intervalError (J : ℕ) (a b : ℝ)
    (e : ℕ → ℂ) (t : ℝ) : ℝ :=
  approxError J e (t - b) + approxError J e (t - a)

theorem abs_intervalSigma_le_one (a b t : ℝ) :
    |intervalSigma a b t| ≤ 1 := by
  have hb0 := Int.fract_nonneg (t - b)
  have hb1 := Int.fract_lt_one (t - b)
  have ha0 := Int.fract_nonneg (t - a)
  have ha1 := Int.fract_lt_one (t - a)
  rw [abs_le]
  constructor <;> dsimp [intervalSigma, saw] <;> linarith

theorem exists_halfOpen_interval_certificate
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ c e : ℕ → ℂ,
      (∀ j ∈ Finset.Icc 1 J,
        ‖c j‖ ≤ (2 : ℝ) / j ∧ ‖e j‖ ≤ (2 : ℝ) / (J + 1)) ∧
      (∀ t : ℝ,
        (if a ≤ Int.fract t ∧ Int.fract t < b then (1 : ℝ) else 0) =
          (b - a) + intervalSigma a b t ∧
        |intervalSigma a b t| ≤ 1 ∧
        |intervalSigma a b t - intervalMain J a b c t| ≤
          intervalError J a b e t ∧
        0 ≤ intervalError J a b e t) := by
  obtain ⟨c, e, hcoeff, hpoint⟩ := positive_pointwise J hJ
  refine ⟨c, e, hcoeff, ?_⟩
  intro t
  have hleft : |saw (t - b) - approxMain J c (t - b)| ≤
      approxError J e (t - b) := hpoint (t - b)
  have hright : |saw (t - a) - approxMain J c (t - a)| ≤
      approxError J e (t - a) := hpoint (t - a)
  have hEleft : 0 ≤ approxError J e (t - b) :=
    (abs_nonneg _).trans hleft
  have hEright : 0 ≤ approxError J e (t - a) :=
    (abs_nonneg _).trans hright
  have herror : |intervalSigma a b t - intervalMain J a b c t| ≤
      intervalError J a b e t := by
    calc
      |intervalSigma a b t - intervalMain J a b c t| =
          |(saw (t - b) - approxMain J c (t - b)) -
            (saw (t - a) - approxMain J c (t - a))| := by
              congr 1
              dsimp [intervalSigma, intervalMain]
              ring
      _ ≤ |saw (t - b) - approxMain J c (t - b)| +
          |saw (t - a) - approxMain J c (t - a)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (saw (t - b) - approxMain J c (t - b))
              (-(saw (t - a) - approxMain J c (t - a))))
      _ ≤ intervalError J a b e t := by
          dsimp [intervalError]
          exact add_le_add hleft hright
  refine ⟨?_, abs_intervalSigma_le_one a b t, herror, ?_⟩
  · dsimp [intervalSigma]
    convert halfOpen_indicator_eq_saw a b t ha hab hb using 1 <;> ring
  · dsimp [intervalError]
    exact add_nonneg hEleft hEright

#print axioms abs_intervalSigma_le_one
#print axioms exists_halfOpen_interval_certificate
end RML.Fourier.Vaaler.Positive
