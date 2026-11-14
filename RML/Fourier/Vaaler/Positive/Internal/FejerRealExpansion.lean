module

public import RML.Fourier.Vaaler.Positive.Internal.FejerTriangleAlgebra

@[expose] public section

open Finset Complex
namespace RML.Fourier.Vaaler.Positive

/-- Exact real Fourier expansion of the geometric square at unit phase. -/
theorem yevorin_fejer_real_triangle (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖yevorin_geom z n‖ ^ 2 =
      ((n + 1 : ℕ) : ℝ) +
      ∑ k ∈ Finset.range n,
        2 * ((n : ℝ) - (k : ℝ)) * (z ^ (k + 1)).re := by
  have hconj :
      star (yevorin_geom z n) = yevorin_geom (star z) n := by
    simp [yevorin_geom, map_sum]
  have hunit : z * star z = 1 := by
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj', hz]
    norm_num
  have htri := yevorin_fejer_triangle_identity z hunit n
  have hnorm :
      ((‖yevorin_geom z n‖ ^ 2 : ℝ) : ℂ) =
      yevorin_geom z n * yevorin_geom (star z) n := by
    rw [← hconj, show star (yevorin_geom z n) =
      (starRingEnd ℂ) (yevorin_geom z n) from rfl,
      Complex.mul_conj']
    norm_cast
  rw [← hnorm] at htri
  have hreal := congrArg Complex.re htri
  simp only [Complex.ofReal_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  have hsum :
      (∑ k ∈ Finset.range n,
        (((n : ℂ) - (k : ℂ)) *
          (z ^ (k + 1) + (star z) ^ (k + 1))).re) =
      ∑ k ∈ Finset.range n,
        2 * ((n : ℝ) - (k : ℝ)) * (z ^ (k + 1)).re := by
    apply Finset.sum_congr rfl
    intro k hk
    have hconjk : ((star z) ^ (k + 1)).re = (z ^ (k + 1)).re := by
      change (((starRingEnd ℂ) z) ^ (k + 1)).re = (z ^ (k + 1)).re
      simpa only [map_pow] using (Complex.conj_re (z ^ (k + 1)))
    simp only [Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.natCast_re, Complex.natCast_im,
      sub_zero, zero_mul, mul_zero, add_zero]
    rw [hconjk]
    ring
  have hReSum (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, ih, Complex.add_re]
  unfold yevorin_triangle at hreal
  rw [hReSum, hsum] at hreal
  simpa using hreal

#print axioms yevorin_fejer_real_triangle
end RML.Fourier.Vaaler.Positive
