module

public import RML.Fourier.Vaaler.Positive.Internal.VaalerFejerModes

@[expose] public section

open Finset
namespace RML.Fourier.Vaaler.Positive
open RML.Fourier.Vaaler.Internal

theorem yevorin_vaaler_error_eq_dirichlet (J : ℕ) (t : ℝ) :
    (1 : ℝ) / ((J + 1 : ℕ) : ℝ) +
      (∑ j ∈ Finset.Icc 1 J,
        (yevorin_vaalerErrorCoeff J j * realVaalerMode j t).re) =
      (1 : ℝ) / (2 * ((J + 1 : ℕ) : ℝ)) +
        ‖h3RealDirichletSum J t‖ ^ 2 /
          (2 * (((J + 1 : ℕ) : ℝ)^2)) := by
  let D : ℝ := ((J + 1 : ℕ) : ℝ)
  let z : ℂ := Complex.exp
    (Complex.I * (((2 * Real.pi * t : ℝ) : ℂ)))
  let S : ℝ := ∑ k ∈ Finset.range J,
    ((J : ℝ) - (k : ℝ)) / D^2 * (z^(k+1)).re
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have hgeom : yevorin_geom z J = h3RealDirichletSum J t := rfl
  have hMode (k : ℕ) :
      (z ^ (k+1)).re = (realVaalerMode (k+1) t).re := by
    congr 1
    dsimp [z]
    exact yevorin_phase_pow_eq_realVaalerMode (k+1) t
  have hsum :
      (∑ j ∈ Finset.Icc 1 J,
        (yevorin_vaalerErrorCoeff J j * realVaalerMode j t).re) = S := by
    rw [yevorin_sum_Icc_one_eq_range]
    dsimp [S]
    apply Finset.sum_congr rfl
    intro k hk
    rw [yevorin_error_mode_triangle]
    rw [← hMode]
  have hscale :
      (∑ k ∈ Finset.range J,
        2 * ((J : ℝ) - (k : ℝ)) * (z ^ (k+1)).re) =
        2 * D^2 * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    field_simp [hDne]
  have htriangle := yevorin_fejer_real_triangle z hz J
  rw [hgeom, hscale] at htriangle
  have htriangle' :
      ‖h3RealDirichletSum J t‖ ^ 2 = D + 2 * D^2 * S := by
    simpa [D] using htriangle
  have hAlgebra (T : ℝ) :
      1/D + T = 1/(2*D) + (D + 2*D^2*T)/(2*D^2) := by
    field_simp [hDne]
    ring
  rw [hsum]
  change 1/D + S =
    1/(2*D) + ‖h3RealDirichletSum J t‖^2/(2*D^2)
  rw [htriangle']
  exact hAlgebra S

#print axioms yevorin_vaaler_error_eq_dirichlet
end RML.Fourier.Vaaler.Positive
