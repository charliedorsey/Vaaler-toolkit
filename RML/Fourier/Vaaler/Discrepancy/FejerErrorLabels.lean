module

public import RML.Fourier.Vaaler.Discrepancy.RealTensorBridge
public import RML.Fourier.Vaaler.Discrepancy.SignedScalar

@[expose] public section

/-!
# Explicit zero and signed frequency labels for (1 + Fejer-error)

This is a proposed proof under verification, NOT yet admitted to
the release umbrella. The zero frequency has coefficient
1 + 2/(J+1), which must not be dropped during tensor expansion.
-/

namespace RML.Fourier.Vaaler.Positive
open Finset

/-- Distinct option label: none = zero frequency, some = signed nonzero. -/
noncomputable def signedErrorOneSupport (J : ℕ) :
    Finset (Option (ℕ × Bool)) :=
  Finset.insertNone (signedPairSupport J)

def signedErrorOneFreq : Option (ℕ × Bool) → ℤ
  | none => 0
  | some p => signedPairFrequency p

noncomputable def signedErrorOneCoeff (J : ℕ) (a b : ℝ) :
    Option (ℕ × Bool) → ℂ
  | none => 1 + (2 : ℂ) / (J + 1)
  | some p => signedErrorCoeff J a b p

/-- Exact finite error-plus-one formula including its zero mode. -/
theorem signedErrorOne_eq_two_sided (J : ℕ) (a b t : ℝ) :
    (((1 + intervalError J a b (errorCoeff J) t : ℝ) : ℂ)) =
      ∑ p ∈ signedErrorOneSupport J,
        signedErrorOneCoeff J a b p *
          signedFourierMode (signedErrorOneFreq p) t := by
  push_cast
  rw [signedError_eq_two_sided]
  simp only [signedErrorOneSupport, Finset.sum_insertNone]
  simp [signedErrorOneCoeff, signedErrorOneFreq, signedFourierMode]
  ring

#print axioms signedErrorOne_eq_two_sided
end RML.Fourier.Vaaler.Positive
