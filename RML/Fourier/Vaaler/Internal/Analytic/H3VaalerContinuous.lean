module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
public import RML.Fourier.Vaaler.Internal.H3VaalerPointwise

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous

open RML.Fourier.Vaaler.Internal

noncomputable def h3TailSum (x : ℝ) : ℝ :=
  ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2

noncomputable def h3InterpBracket (x : ℝ) : ℝ :=
  (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) -
    h3TailSum x + 2 * x⁻¹

noncomputable def h3InterpH (x : ℝ) : ℝ :=
  if Real.sin (Real.pi * x) = 0 then Real.sign x
  else (Real.sin (Real.pi * x) / Real.pi) ^ 2 * h3InterpBracket x

noncomputable def h3G (x : ℝ) : ℝ :=
  if x = 0 then 1 else
  (Real.sin (Real.pi * x) / Real.pi) *
      (Real.cos (Real.pi * x) * Real.pi / Real.pi) * h3InterpBracket x
    + (1 / 2) * (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
          (x - (k + 1 : ℕ))⁻¹)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
            (x + (k + 1 : ℕ))⁻¹)
          + 2 * (-(x⁻¹ ^ 2))))

noncomputable def h3GC (x : ℝ) : ℂ := (h3G x : ℂ)

noncomputable def h3HNcore (N : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ Finset.range N,
    (h3VaalerK (z - ((m : ℝ) + 1)) -
      h3VaalerK (z + ((m : ℝ) + 1)))

noncomputable def h3TailFn (z : ℝ) : ℝ :=
  (Real.sin (Real.pi * z) / Real.pi) ^ 2 * (2 * z⁻¹)

noncomputable def h3CesaroCore (M : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M,
    (1 - (((m + 1 : ℕ) : ℝ) / (M : ℝ))) *
      (h3VaalerK (z - ((m : ℝ) + 1)) -
        h3VaalerK (z + ((m : ℝ) + 1)))

noncomputable def h3GSharp (N : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (h3HNcore N) x +
    (1 / 2 : ℝ) * deriv h3TailFn x : ℝ)

noncomputable def h3GCes (M : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (h3CesaroCore M) x +
    (1 / 2 : ℝ) * deriv h3TailFn x : ℝ)

@[simp] theorem h3GC_re (x : ℝ) : (h3GC x).re = h3G x := by
  simp [h3GC]

theorem h3G_zero : h3G 0 = 1 := by
  simp [h3G]

theorem h3G_eq_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    h3G x =
      (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * h3InterpBracket x
        + (1 / 2) * (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 *
              (x - (k + 1 : ℕ))⁻¹)
            + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 *
                (x + (k + 1 : ℕ))⁻¹)
              + 2 * (-(x⁻¹ ^ 2)))) := by
  simp [h3G, hx]

#print axioms h3G_eq_of_ne_zero

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerContinuous
