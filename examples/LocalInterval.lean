module

public import RML.Fourier.Vaaler.Toolkit

@[expose] public section

open RML.Fourier.Vaaler.Positive

example (J : ℕ) (hJ : 1 ≤ J) :
    ∃ c e : ℕ → ℂ,
      (∀ j ∈ Finset.Icc 1 J,
        ‖c j‖ ≤ (2 : ℝ) / j ∧ ‖e j‖ ≤ (2 : ℝ) / (J + 1)) ∧
      (∀ t : ℝ,
        (if (0 : ℝ) ≤ Int.fract t ∧ Int.fract t < 1 / 2 then (1 : ℝ) else 0) =
          (1 / 2 - 0) + intervalSigma 0 (1 / 2) t ∧
        |intervalSigma 0 (1 / 2) t| ≤ 1 ∧
        |intervalSigma 0 (1 / 2) t - intervalMain J 0 (1 / 2) c t| ≤
          intervalError J 0 (1 / 2) e t ∧
        0 ≤ intervalError J 0 (1 / 2) e t) := by
  apply exists_halfOpen_interval_certificate J hJ 0 (1 / 2)
  all_goals norm_num
