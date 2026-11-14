module

public import RML.Fourier.Vaaler.Positive.ExplicitPointwise
public import RML.Fourier.Vaaler.Discrepancy.LocalInterval

@[expose] public section

/-! Public named-coefficient interval certificate, with no existential choices. -/

namespace RML.Fourier.Vaaler.Positive

theorem explicit_halfOpen_interval_certificate
    (J : ℕ) (hJ : 1 ≤ J) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (t : ℝ) :
      (if a ≤ Int.fract t ∧ Int.fract t < b then (1 : ℝ) else 0) =
        (b - a) + intervalSigma a b t ∧
      |intervalSigma a b t| ≤ 1 ∧
      |intervalSigma a b t -
         intervalMain J a b (mainCoeff J) t| ≤
        intervalError J a b (errorCoeff J) t ∧
      0 ≤ intervalError J a b (errorCoeff J) t := by
  have hleft : |saw (t - b) - approxMain J (mainCoeff J) (t - b)| ≤
      approxError J (errorCoeff J) (t - b) := by
    simpa only [approxMain, approxError] using
      explicit_positive_pointwise J hJ (t - b)
  have hright : |saw (t - a) - approxMain J (mainCoeff J) (t - a)| ≤
      approxError J (errorCoeff J) (t - a) := by
    simpa only [approxMain, approxError] using
      explicit_positive_pointwise J hJ (t - a)
  have hEleft : 0 ≤ approxError J (errorCoeff J) (t - b) :=
    (abs_nonneg _).trans hleft
  have hEright : 0 ≤ approxError J (errorCoeff J) (t - a) :=
    (abs_nonneg _).trans hright
  have herror :
      |intervalSigma a b t - intervalMain J a b (mainCoeff J) t| ≤
        intervalError J a b (errorCoeff J) t := by
    calc
      |intervalSigma a b t - intervalMain J a b (mainCoeff J) t| =
          |(saw (t - b) - approxMain J (mainCoeff J) (t - b)) -
            (saw (t - a) - approxMain J (mainCoeff J) (t - a))| := by
              congr 1
              dsimp [intervalSigma, intervalMain]
              ring
      _ ≤ |saw (t - b) - approxMain J (mainCoeff J) (t - b)| +
          |saw (t - a) - approxMain J (mainCoeff J) (t - a)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (saw (t - b) - approxMain J (mainCoeff J) (t - b))
              (-(saw (t - a) - approxMain J (mainCoeff J) (t - a))))
      _ ≤ intervalError J a b (errorCoeff J) t := by
          dsimp [intervalError]
          exact add_le_add hleft hright
  refine ⟨?_, abs_intervalSigma_le_one a b t, herror, ?_⟩
  · dsimp [intervalSigma]
    convert halfOpen_indicator_eq_saw a b t ha hab hb using 1 <;> ring
  · dsimp [intervalError]
    exact add_nonneg hEleft hEright

#print axioms explicit_halfOpen_interval_certificate
end RML.Fourier.Vaaler.Positive
