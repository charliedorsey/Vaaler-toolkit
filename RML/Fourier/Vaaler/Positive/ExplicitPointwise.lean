module

public import RML.Fourier.Vaaler.Positive.Coefficients
public import RML.Fourier.Vaaler.Positive.Internal.VaalerFullPointwise

@[expose] public section

/-!
# Constructive positive Vaaler certificate
This is the explicit coefficient witness of the existing Vaaler pointwise
result, extracted into a public theorem so downstream consumers can use the
literal mainCoeff and errorCoeff, not merely existential coefficients.
The proof repeats the existing source-faithful split at integer jumps
without changing or weakening the historical source theorem.
-/

open Finset
namespace RML.Fourier.Vaaler.Positive
open RML.Fourier.Vaaler.Internal

private theorem vaaler_explicit_mode_sum_fract (J : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ j ∈ Finset.Icc 1 J, (a j * realVaalerMode j t).re) =
    (∑ j ∈ Finset.Icc 1 J, (a j * realVaalerMode j (Int.fract t)).re) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [yevorin_mode_fract]

private theorem vaaler_explicit_main_zero (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J,
      (yevorin_vaalerMainCoeff J j * realVaalerMode j 0).re) = 0 := by
  rw [yevorin_vaalerMainCoeff_sum_eq_poly, h3VaalerPolyReal_eq_sineSum]
  simp

private theorem vaaler_explicit_dirichlet_zero (J : ℕ) :
    h3RealDirichletSum J 0 = ((J + 1 : ℕ) : ℂ) := by
  unfold h3RealDirichletSum
  simp

/-- Explicit Vaaler coefficients certify the global centered sawtooth error,
    INCLUDING integer-grid jumps. -/
theorem explicit_positive_pointwise_internal (J : ℕ) (hJ : 1 ≤ J) (t : ℝ) :
    |saw t - ∑ j ∈ Finset.Icc 1 J,
      (yevorin_vaalerMainCoeff J j * realVaalerMode j t).re| ≤
    (1 : ℝ) / (J + 1) +
      ∑ j ∈ Finset.Icc 1 J,
        (yevorin_vaalerErrorCoeff J j * realVaalerMode j t).re := by
  let x := Int.fract t
  have hmain := vaaler_explicit_mode_sum_fract J (yevorin_vaalerMainCoeff J) t
  have herr := vaaler_explicit_mode_sum_fract J (yevorin_vaalerErrorCoeff J) t
  have hDpos : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by positivity
  have hDne : (((J + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hDpos
  have hsaw : saw t = x - 1/2 := by rfl
  rw [hsaw, hmain, herr, yevorin_vaalerMainCoeff_sum_eq_poly]
  change |x - 1/2 - (h3VaalerPolyReal J x).re| ≤
    1 / ((J : ℝ) + 1) +
      ∑ j ∈ Finset.Icc 1 J,
        (yevorin_vaalerErrorCoeff J j * realVaalerMode j x).re
  by_cases hx : x = 0
  · rw [hx]
    have hMain0 := vaaler_explicit_main_zero J
    rw [yevorin_vaalerMainCoeff_sum_eq_poly] at hMain0
    rw [hMain0]
    have hError0 := yevorin_vaaler_error_eq_dirichlet J 0
    simp only [Nat.cast_add, Nat.cast_one] at hError0
    have hD0 := vaaler_explicit_dirichlet_zero J
    rw [hError0, hD0]
    have hNorm : ‖((J + 1 : ℕ) : ℂ)‖ =
        ((J + 1 : ℕ) : ℝ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Complex.norm_natCast (J + 1))
    rw [hNorm]
    have hOneHalf : (1 : ℝ)/2 ≤
        1/(2 * ((J + 1 : ℕ) : ℝ)) +
        ((J + 1 : ℕ) : ℝ)^2 /
          (2 * (((J + 1 : ℕ) : ℝ)^2)) := by
      field_simp
      nlinarith [hDpos]
    simpa using hOneHalf
  · have hx0 : 0 < x :=
      lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hx)
    have hx1 : x < 1 := Int.fract_lt_one t
    have hxnonint : ¬ ∃ m : ℤ, x = (m : ℝ) := by
      rintro ⟨m, hm⟩
      have hm0 : (0 : ℝ) < (m : ℝ) := by rw [← hm]; exact hx0
      have hm1 : (m : ℝ) < 1 := by rw [← hm]; exact hx1
      have hmge : (1 : ℤ) ≤ m := by
        have hmp : (0 : ℤ) < m := by exact_mod_cast hm0
        omega
      have hmger : (1 : ℝ) ≤ m := by exact_mod_cast hmge
      linarith
    have hInterior := yevorin_vaaler_real_interior_abs J x hx0 hx1
    have hF := h3RealFejerClosed_eq_dirichletNormSq J (x := x) hxnonint
    rw [hF] at hInterior
    have hError := yevorin_vaaler_error_eq_dirichlet J x
    calc
      |x - 1/2 - (h3VaalerPolyReal J x).re| =
        |(h3VaalerPolyReal J x).re - (x - 1/2)| := by rw [abs_sub_comm]
      _ ≤ (((J + 1 : ℕ) : ℝ))⁻¹ *
          ‖h3RealDirichletSum J x‖ ^ 2 /
            (2 * ((J + 1 : ℕ) : ℝ)) := hInterior
      _ = ‖h3RealDirichletSum J x‖ ^ 2 /
          (2 * (((J + 1 : ℕ) : ℝ)^2)) := by
            field_simp [hDne]
      _ ≤ 1/(2 * ((J + 1 : ℕ) : ℝ)) +
            ‖h3RealDirichletSum J x‖ ^ 2 /
              (2 * (((J + 1 : ℕ) : ℝ)^2)) := by
                apply le_add_of_nonneg_left
                positivity
      _ = _ := by simpa only [Nat.cast_add, Nat.cast_one] using hError.symm

/-- Main public endpoint-correct constructive result, using the named API. -/
theorem explicit_positive_pointwise (J : ℕ) (hJ : 1 ≤ J) (t : ℝ) :
    |saw t - ∑ j ∈ Finset.Icc 1 J,
      (mainCoeff J j * realVaalerMode j t).re| ≤
    (1 : ℝ) / (J + 1) +
      ∑ j ∈ Finset.Icc 1 J,
        (errorCoeff J j * realVaalerMode j t).re := by
  simpa only [mainCoeff, errorCoeff] using
    explicit_positive_pointwise_internal J hJ t

#print axioms explicit_positive_pointwise_internal
#print axioms explicit_positive_pointwise
end RML.Fourier.Vaaler.Positive
