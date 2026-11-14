module

public import Mathlib

@[expose] public section

/-!
Canonical candidate: exact source-definition mirror from the pinned toolkit.
The proof hole appears ONLY in this Challenge file.
Do not modify generated definitions: run scripts/check_palomar_challenge_mirror.py.
-/

namespace RML.Fourier.Vaaler.Internal


-- Source: RML/Fourier/Vaaler/Internal/H3VaalerCoeff.lean :: h3VaalerJHat

noncomputable def h3VaalerJHat (J : ℕ) (n : ℤ) : ℝ :=
  if n = 0 then 1 else if n.natAbs ≤ J then
    let t : ℝ := (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
    Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t
  else 0

end RML.Fourier.Vaaler.Internal

namespace RML.Fourier.Vaaler.Positive

open RML.Fourier.Vaaler.Internal


-- Source: RML/Fourier/Vaaler/Positive/Core.lean :: saw

noncomputable def saw (t : ℝ) : ℝ := Int.fract t - 1 / 2


-- Source: RML/Fourier/Vaaler/Positive/Core.lean :: realVaalerMode

noncomputable def realVaalerMode (j : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ)))


-- Source: RML/Fourier/Vaaler/Positive/Internal/VaalerCoefficients.lean :: yevorin_vaalerMainCoeff

noncomputable def yevorin_vaalerMainCoeff (J j : ℕ) : ℂ :=
  (((h3VaalerJHat J (j : ℤ) / (Real.pi * (j : ℝ))) : ℝ) : ℂ) *
    Complex.I


-- Source: RML/Fourier/Vaaler/Positive/Internal/VaalerCoefficients.lean :: yevorin_vaalerErrorCoeff

noncomputable def yevorin_vaalerErrorCoeff (J j : ℕ) : ℂ :=
  (((1 - (j : ℝ) / ((J + 1 : ℕ) : ℝ)) /
      ((J + 1 : ℕ) : ℝ) : ℝ) : ℂ)


-- Source: RML/Fourier/Vaaler/Positive/Coefficients.lean :: mainCoeff

noncomputable abbrev mainCoeff (J j : ℕ) : ℂ :=
  yevorin_vaalerMainCoeff J j


-- Source: RML/Fourier/Vaaler/Positive/Coefficients.lean :: errorCoeff

noncomputable abbrev errorCoeff (J j : ℕ) : ℂ :=
  yevorin_vaalerErrorCoeff J j


-- Source: RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean :: approxMain

noncomputable def approxMain (J : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, (c j * realVaalerMode j t).re


-- Source: RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean :: approxError

noncomputable def approxError (J : ℕ) (e : ℕ → ℂ) (t : ℝ) : ℝ :=
  (1 : ℝ) / (J + 1) +
    ∑ j ∈ Finset.Icc 1 J, (e j * realVaalerMode j t).re


-- Source: RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean :: intervalSigma

noncomputable def intervalSigma (a b t : ℝ) : ℝ :=
  saw (t - b) - saw (t - a)


-- Source: RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean :: intervalMain

noncomputable def intervalMain (J : ℕ) (a b : ℝ)
    (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  approxMain J c (t - b) - approxMain J c (t - a)


-- Source: RML/Fourier/Vaaler/Discrepancy/LocalInterval.lean :: intervalError

noncomputable def intervalError (J : ℕ) (a b : ℝ)
    (e : ℕ → ℂ) (t : ℝ) : ℝ :=
  approxError J e (t - b) + approxError J e (t - a)


-- Source: RML/Fourier/Vaaler/Discrepancy/TorusBox.lean :: torusArcLength

noncomputable def torusArcLength (a b : ℝ) : ℝ :=
  if a < b then b - a else 1 + b - a


-- Source: RML/Fourier/Vaaler/Discrepancy/TorusBox.lean :: torusArcIndicator

noncomputable def torusArcIndicator (a b t : ℝ) : ℝ :=
  if a < b then
    (if a ≤ Int.fract t ∧ Int.fract t < b then 1 else 0)
  else
    (if a ≤ Int.fract t ∨ Int.fract t < b then 1 else 0)

end RML.Fourier.Vaaler.Positive


namespace VaalerETKChallenge

open Finset
open RML.Fourier.Vaaler.Positive

/-- Formal challenge: prove the exact signed-weight box ETK
bound with |w| on every approximation error term. -/
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
  sorry

end VaalerETKChallenge
