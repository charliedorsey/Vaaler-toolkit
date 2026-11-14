module

public import RML.Fourier.Vaaler.Positive.Internal.VaalerCoefficients

@[expose] public section

/-!
Public facade prototype for the already-verified internal positive-frequency
Vaaler coefficients. New module, not a modification to frozen R0002 sources.

This exposes the coefficients and their norm control. It does NOT claim
that the explicit coefficients close the full global pointwise approximation
until a separate theorem is kernel-compiled and audited.
-/
namespace RML.Fourier.Vaaler.Positive

/-- The positive-frequency coefficient of the centered sawtooth approximant. -/
noncomputable abbrev mainCoeff (J j : ℕ) : ℂ :=
  yevorin_vaalerMainCoeff J j

/-- The positive-frequency coefficient of the Fejér error polynomial. -/
noncomputable abbrev errorCoeff (J j : ℕ) : ℂ :=
  yevorin_vaalerErrorCoeff J j

/-- Coefficient bounds inherited from the original source-exact proof. -/
theorem mainCoeff_norm_le (J j : ℕ) (hj : 1 ≤ j) :
    ‖mainCoeff J j‖ ≤ (2 : ℝ) / j :=
  yevorin_vaalerMainCoeff_norm_le J j hj

theorem errorCoeff_norm_le (J j : ℕ)
    (hj : j ∈ Finset.Icc 1 J) :
    ‖errorCoeff J j‖ ≤ (2 : ℝ) / (J + 1) :=
  yevorin_vaalerErrorCoeff_norm_le J j hj

/-- Identifies the explicit sum with the historically certified sine polynomial. -/
theorem mainCoeff_sum_eq_poly (J : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.Icc 1 J,
      (mainCoeff J j * realVaalerMode j t).re) =
      (RML.Fourier.Vaaler.Internal.h3VaalerPolyReal J t).re :=
  yevorin_vaalerMainCoeff_sum_eq_poly J t

#print axioms mainCoeff_norm_le
#print axioms errorCoeff_norm_le
#print axioms mainCoeff_sum_eq_poly
end RML.Fourier.Vaaler.Positive
