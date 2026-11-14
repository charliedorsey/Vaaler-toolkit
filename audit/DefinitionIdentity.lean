module

public import RML.Fourier.Vaaler.Toolkit

@[expose] public section

/-! Generated kernel equality obligations for source-derived definitions. -/
namespace VaalerETKShadow.Internal


-- Source: RML/Fourier/Vaaler/Internal/H3VaalerCoeff.lean :: h3VaalerJHat

noncomputable def h3VaalerJHat (J : ℕ) (n : ℤ) : ℝ :=
  if n = 0 then 1 else if n.natAbs ≤ J then
    let t : ℝ := (n.natAbs : ℝ) / (((J + 1 : ℕ) : ℝ))
    Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t
  else 0

end VaalerETKShadow.Internal

namespace VaalerETKShadow.Positive

open VaalerETKShadow.Internal


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

end VaalerETKShadow.Positive


theorem vaaler_etk_definition_identity_h3VaalerJHat :
    RML.Fourier.Vaaler.Internal.h3VaalerJHat = VaalerETKShadow.Internal.h3VaalerJHat := by rfl
#print axioms vaaler_etk_definition_identity_h3VaalerJHat

theorem vaaler_etk_definition_identity_saw :
    RML.Fourier.Vaaler.Positive.saw = VaalerETKShadow.Positive.saw := by rfl
#print axioms vaaler_etk_definition_identity_saw

theorem vaaler_etk_definition_identity_realVaalerMode :
    RML.Fourier.Vaaler.Positive.realVaalerMode = VaalerETKShadow.Positive.realVaalerMode := by rfl
#print axioms vaaler_etk_definition_identity_realVaalerMode

theorem vaaler_etk_definition_identity_yevorin_vaalerMainCoeff :
    RML.Fourier.Vaaler.Positive.yevorin_vaalerMainCoeff = VaalerETKShadow.Positive.yevorin_vaalerMainCoeff := by rfl
#print axioms vaaler_etk_definition_identity_yevorin_vaalerMainCoeff

theorem vaaler_etk_definition_identity_yevorin_vaalerErrorCoeff :
    RML.Fourier.Vaaler.Positive.yevorin_vaalerErrorCoeff = VaalerETKShadow.Positive.yevorin_vaalerErrorCoeff := by rfl
#print axioms vaaler_etk_definition_identity_yevorin_vaalerErrorCoeff

theorem vaaler_etk_definition_identity_mainCoeff :
    RML.Fourier.Vaaler.Positive.mainCoeff = VaalerETKShadow.Positive.mainCoeff := by rfl
#print axioms vaaler_etk_definition_identity_mainCoeff

theorem vaaler_etk_definition_identity_errorCoeff :
    RML.Fourier.Vaaler.Positive.errorCoeff = VaalerETKShadow.Positive.errorCoeff := by rfl
#print axioms vaaler_etk_definition_identity_errorCoeff

theorem vaaler_etk_definition_identity_approxMain :
    RML.Fourier.Vaaler.Positive.approxMain = VaalerETKShadow.Positive.approxMain := by rfl
#print axioms vaaler_etk_definition_identity_approxMain

theorem vaaler_etk_definition_identity_approxError :
    RML.Fourier.Vaaler.Positive.approxError = VaalerETKShadow.Positive.approxError := by rfl
#print axioms vaaler_etk_definition_identity_approxError

theorem vaaler_etk_definition_identity_intervalSigma :
    RML.Fourier.Vaaler.Positive.intervalSigma = VaalerETKShadow.Positive.intervalSigma := by rfl
#print axioms vaaler_etk_definition_identity_intervalSigma

theorem vaaler_etk_definition_identity_intervalMain :
    RML.Fourier.Vaaler.Positive.intervalMain = VaalerETKShadow.Positive.intervalMain := by rfl
#print axioms vaaler_etk_definition_identity_intervalMain

theorem vaaler_etk_definition_identity_intervalError :
    RML.Fourier.Vaaler.Positive.intervalError = VaalerETKShadow.Positive.intervalError := by rfl
#print axioms vaaler_etk_definition_identity_intervalError

theorem vaaler_etk_definition_identity_torusArcLength :
    RML.Fourier.Vaaler.Positive.torusArcLength = VaalerETKShadow.Positive.torusArcLength := by rfl
#print axioms vaaler_etk_definition_identity_torusArcLength

theorem vaaler_etk_definition_identity_torusArcIndicator :
    RML.Fourier.Vaaler.Positive.torusArcIndicator = VaalerETKShadow.Positive.torusArcIndicator := by rfl
#print axioms vaaler_etk_definition_identity_torusArcIndicator
