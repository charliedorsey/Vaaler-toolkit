module

public import RML.Fourier.Vaaler.Discrepancy.OneDimETK
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite signed complex tensor characters
An explicit reusable conversion from products of *finite* one-coordinate
complex exponential polynomials to the standard weighted sum
S(h) = sum_n w_n exp(2*pi*i*sum_i h_i*x_{n,i}).
No analytic approximation or infinite series appears here.
-/

namespace RML.Fourier.Vaaler.Positive

open Finset

/-- The integer-frequency tensor character. -/
noncomputable def signedTensorMode
    {κ : Type*} [Fintype κ]
    (h : κ → ℤ) (t : κ → ℝ) : ℂ :=
  ∏ i, signedFourierMode (h i) (t i)

/-- The conventional exp(2*pi*i*dot(h,t)) tensor character. -/
noncomputable def signedTensorDotMode
    {κ : Type*} [Fintype κ]
    (h : κ → ℤ) (t : κ → ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * Real.pi * Complex.I *
    ∑ i, (h i : ℂ) * (t i : ℂ))

theorem signedTensorMode_eq_dot
    {κ : Type*} [Fintype κ]
    (h : κ → ℤ) (t : κ → ℝ) :
    signedTensorMode h t = signedTensorDotMode h t := by
  classical
  unfold signedTensorMode signedTensorDotMode signedFourierMode
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The standard weighted signed complex exponential sum. -/
noncomputable def weightedTensorExponentialSum
    {κ ι : Type*} [Fintype κ]
    (N : Finset ι) (w : ι → ℝ)
    (x : ι → κ → ℝ) (h : κ → ℤ) : ℂ :=
  ∑ n ∈ N, (w n : ℂ) * signedTensorDotMode h (x n)

/-- Exact finite product expansion with coordinate-dependent integer
frequencies and coefficients; the RHS uses the standard S(h). -/
theorem weighted_tensor_expansion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : κ → Finset ℤ) (c : κ → ℤ → ℂ) :
    (∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ h ∈ C i, c i h * signedFourierMode h (x n i)) =
    ∑ h ∈ Fintype.piFinset C,
      (∏ i, c i (h i)) * weightedTensorExponentialSum N w x h := by
  classical
  simp_rw [Finset.prod_univ_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  unfold weightedTensorExponentialSum
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← signedTensorMode_eq_dot]
  unfold signedTensorMode
  rw [Finset.prod_mul_distrib]
  ring

/-- Consumer-ready norm bound for a finite signed complex frequency box. -/
theorem weighted_tensor_norm_le_exponential_sums
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (N : Finset ι) (w : ι → ℝ) (x : ι → κ → ℝ)
    (C : κ → Finset ℤ) (c : κ → ℤ → ℂ) :
    ‖∑ n ∈ N, (w n : ℂ) *
       ∏ i, ∑ h ∈ C i, c i h * signedFourierMode h (x n i)‖ ≤
    ∑ h ∈ Fintype.piFinset C,
      (∏ i, ‖c i (h i)‖) * ‖weightedTensorExponentialSum N w x h‖ := by
  rw [weighted_tensor_expansion]
  calc
    ‖∑ h ∈ Fintype.piFinset C,
      (∏ i, c i (h i)) * weightedTensorExponentialSum N w x h‖ ≤
      ∑ h ∈ Fintype.piFinset C,
        ‖(∏ i, c i (h i)) * weightedTensorExponentialSum N w x h‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [norm_mul, norm_prod]

#print axioms signedTensorMode_eq_dot
#print axioms weighted_tensor_expansion
#print axioms weighted_tensor_norm_le_exponential_sums

end RML.Fourier.Vaaler.Positive
