module

public import Mathlib

@[expose] public section

open Finset

namespace RML.Fourier.Vaaler.Positive

noncomputable def yevorin_geom (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), z ^ k

noncomputable def yevorin_triangle (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n,
    (((n : ℂ) - (k : ℂ)) * (z ^ (k + 1) + (star z) ^ (k + 1)))

private theorem yevorin_geom_succ (z : ℂ) (n : ℕ) :
    yevorin_geom z (n + 1) = yevorin_geom z n + z ^ (n + 1) := by
  simp only [yevorin_geom, show n + 1 + 1 = (n + 1) + 1 by omega,
    Finset.sum_range_succ]

private theorem yevorin_geom_succ_mul (z : ℂ) (n : ℕ) :
    yevorin_geom z (n + 1) = z * yevorin_geom z n + 1 := by
  simp only [yevorin_geom, geom_sum_succ]

/-- A geometric sum reflected across its top exponent. -/
private theorem yevorin_geom_cross (z : ℂ) (hz : z * star z = 1) (n : ℕ) :
    z ^ (n + 1) * yevorin_geom (star z) n = z * yevorin_geom z n := by
  induction n with
  | zero => simp [yevorin_geom]
  | succ n ih =>
      have hlast : z ^ (n + 2) * (star z) ^ (n + 1) = z := by
        calc
          _ = z * (z * star z) ^ (n + 1) := by
            rw [mul_pow]
            simp only [pow_succ]
            ring
          _ = z := by rw [hz]; simp
      calc
        z ^ (n + 2) * yevorin_geom (star z) (n + 1) =
          z ^ (n + 2) * (yevorin_geom (star z) n + (star z) ^ (n + 1)) := by
            rw [yevorin_geom_succ]
        _ = z * (z ^ (n + 1) * yevorin_geom (star z) n) + z := by
            rw [mul_add, hlast]
            simp only [pow_succ]
            ring
        _ = z * (z * yevorin_geom z n) + z := by rw [ih]
        _ = z * yevorin_geom z (n + 1) := by
            rw [yevorin_geom_succ_mul]
            ring

private theorem yevorin_triangle_succ (z : ℂ) (n : ℕ) :
    yevorin_triangle z (n + 1) =
      yevorin_triangle z n +
        ∑ k ∈ Finset.range (n + 1),
          (z ^ (k + 1) + (star z) ^ (k + 1)) := by
  have hrewrite :
      (∑ k ∈ Finset.range n,
        (((n + 1 : ℕ) : ℂ) - (k : ℂ)) *
          (z ^ (k + 1) + (star z) ^ (k + 1))) =
      (∑ k ∈ Finset.range n,
        (((n : ℂ) - (k : ℂ)) *
          (z ^ (k + 1) + (star z) ^ (k + 1)) +
          (z ^ (k + 1) + (star z) ^ (k + 1)))) := by
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  unfold yevorin_triangle
  rw [Finset.sum_range_succ]
  rw [hrewrite, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ]
  push_cast
  ring

private theorem yevorin_geom_mode_sum (z : ℂ) (n : ℕ) :
    z * yevorin_geom z n + star z * yevorin_geom (star z) n =
      ∑ k ∈ Finset.range (n + 1),
        (z ^ (k + 1) + (star z) ^ (k + 1)) := by
  unfold yevorin_geom
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [pow_succ]
  ring

/-- Finite Fejer triangle identity, valid for every unit complex phase. -/
theorem yevorin_fejer_triangle_identity (z : ℂ) (hz : z * star z = 1)
    (n : ℕ) :
    yevorin_geom z n * yevorin_geom (star z) n =
      ((n + 1 : ℕ) : ℂ) + yevorin_triangle z n := by
  induction n with
  | zero => simp [yevorin_geom, yevorin_triangle]
  | succ n ih =>
      have hstarunit : (star z) * star (star z) = 1 := by
        simpa [mul_comm] using hz
      have hcr : z ^ (n + 1) * yevorin_geom (star z) n =
        z * yevorin_geom z n := yevorin_geom_cross z hz n
      have hcr' : (star z) ^ (n + 1) * yevorin_geom z n =
        (star z) * yevorin_geom (star z) n := by
          simpa using yevorin_geom_cross (star z) hstarunit n
      have hp : z ^ (n + 1) * (star z) ^ (n + 1) = 1 := by
        rw [← mul_pow, hz]
        simp
      calc
        yevorin_geom z (n + 1) * yevorin_geom (star z) (n + 1) =
          yevorin_geom z n * yevorin_geom (star z) n +
            (z * yevorin_geom z n + star z * yevorin_geom (star z) n) + 1 := by
              rw [yevorin_geom_succ, yevorin_geom_succ]
              calc
                _ = yevorin_geom z n * yevorin_geom (star z) n +
                    (z ^ (n + 1) * yevorin_geom (star z) n +
                      (star z) ^ (n + 1) * yevorin_geom z n) +
                    z ^ (n + 1) * (star z) ^ (n + 1) := by ring
                _ = _ := by rw [hcr, hcr', hp]
        _ = (((n + 1 : ℕ) : ℂ) + yevorin_triangle z n) +
            (∑ k ∈ Finset.range (n + 1),
              (z ^ (k + 1) + (star z) ^ (k + 1))) + 1 := by
              rw [ih, yevorin_geom_mode_sum]
        _ = (((n + 1 + 1 : ℕ) : ℂ) + yevorin_triangle z (n + 1)) := by
              rw [yevorin_triangle_succ]
              push_cast
              ring

#print axioms yevorin_fejer_triangle_identity
end RML.Fourier.Vaaler.Positive
