module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped BigOperators ContDiff

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv

def HNcore (N : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ Finset.range N,
    (h3VaalerK (z - ((m : ℝ) + 1)) -
      h3VaalerK (z + ((m : ℝ) + 1)))

def cesaroCore (M : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M,
    (1 - ((m : ℝ) + 1) / (M : ℝ)) *
      (h3VaalerK (z - ((m : ℝ) + 1)) -
        h3VaalerK (z + ((m : ℝ) + 1)))

def tailFn (z : ℝ) : ℝ := 2 * z * h3VaalerK z

def gSharp (N : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (HNcore N) x +
    (1 / 2 : ℝ) * deriv tailFn x : ℝ)

def gCes (M : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (cesaroCore M) x +
    (1 / 2 : ℝ) * deriv tailFn x : ℝ)

theorem double_sum_triangular (a : ℕ → ℝ) (M : ℕ) :
    (∑ N ∈ Finset.range M, ∑ m ∈ Finset.range N, a m) =
      ∑ m ∈ Finset.range M,
        ((M : ℝ) - ((m : ℝ) + 1)) * a m := by
  induction M with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ
      (f := fun m => ((↑(K + 1) : ℝ) - ((m : ℝ) + 1)) * a m)]
    have htop :
        ((↑(K + 1) : ℝ) - ((K : ℝ) + 1)) * a K = 0 := by
      push_cast
      ring
    have hsplit :
        (∑ m ∈ Finset.range K,
          ((↑(K + 1) : ℝ) - ((m : ℝ) + 1)) * a m) =
        (∑ m ∈ Finset.range K,
          ((K : ℝ) - ((m : ℝ) + 1)) * a m) +
          ∑ m ∈ Finset.range K, a m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      push_cast
      ring
    rw [hsplit, htop]
    ring

theorem cesaroCore_eq_average (M : ℕ) (z : ℝ) :
    cesaroCore M z =
      (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, HNcore N z := by
  set a : ℕ → ℝ := fun m =>
    h3VaalerK (z - ((m : ℝ) + 1)) -
      h3VaalerK (z + ((m : ℝ) + 1)) with ha
  have hHN :
      (∑ N ∈ Finset.range M, HNcore N z) =
        ∑ N ∈ Finset.range M, ∑ m ∈ Finset.range N, a m := by
    refine Finset.sum_congr rfl (fun N _ => ?_)
    rw [HNcore]
  rw [hHN, double_sum_triangular a M, Finset.mul_sum, cesaroCore]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have hMne : (M : ℝ) ≠ 0 := by
    have hM : 0 < M := Nat.pos_of_ne_zero (by
      rintro rfl
      simp at hm)
    exact_mod_cast hM.ne'
  field_simp [hMne]
  ring

theorem contDiff_HNcore (N : ℕ) : ContDiff ℝ ∞ (HNcore N) := by
  unfold HNcore
  refine ContDiff.sum (fun m _ => ?_)
  have hsubMap : ContDiff ℝ ∞
      (fun z : ℝ => z - ((m : ℝ) + 1)) := by
    exact contDiff_id.sub contDiff_const
  have haddMap : ContDiff ℝ ∞
      (fun z : ℝ => z + ((m : ℝ) + 1)) := by
    exact contDiff_id.add contDiff_const
  exact (contDiff_h3VaalerK.comp hsubMap).sub
    (contDiff_h3VaalerK.comp haddMap)

theorem deriv_cesaroCore_eq (M : ℕ) (x : ℝ) :
    deriv (cesaroCore M) x =
      (1 / (M : ℝ)) *
        ∑ N ∈ Finset.range M, deriv (HNcore N) x := by
  have hfun : cesaroCore M =
      fun z : ℝ => (1 / (M : ℝ)) *
        ∑ N ∈ Finset.range M, HNcore N z := by
    funext z
    exact cesaroCore_eq_average M z
  have hdiff : ∀ N ∈ Finset.range M,
      DifferentiableAt ℝ (HNcore N) x :=
    fun N _ =>
      ((contDiff_HNcore N).differentiable (by simp)).differentiableAt
  rw [hfun, deriv_const_mul]
  · congr 1
    have hsumfun :
        (fun z : ℝ => ∑ N ∈ Finset.range M, HNcore N z) =
          (∑ N ∈ Finset.range M, HNcore N) := by
      funext z
      rw [Finset.sum_apply]
    rw [hsumfun, deriv_sum hdiff]
  · have hsumfun :
        (fun z : ℝ => ∑ N ∈ Finset.range M, HNcore N z) =
          (∑ N ∈ Finset.range M, HNcore N) := by
      funext z
      rw [Finset.sum_apply]
    rw [hsumfun]
    exact DifferentiableAt.sum hdiff

theorem gCes_eq_average_gSharp
    (M : ℕ) (hM : 0 < M) (x : ℝ) :
    gCes M x =
      (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, gSharp N x := by
  have hMne : (M : ℝ) ≠ 0 := by
    exact_mod_cast hM.ne'
  have hreal :
      (1 / 2 : ℝ) * deriv (cesaroCore M) x +
        (1 / 2 : ℝ) * deriv tailFn x =
      (1 / (M : ℝ)) * ∑ N ∈ Finset.range M,
        ((1 / 2 : ℝ) * deriv (HNcore N) x +
          (1 / 2 : ℝ) * deriv tailFn x) := by
    rw [deriv_cesaroCore_eq M x]
    rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    rw [mul_add]
    have h1 :
        (1 / (M : ℝ)) *
            ∑ N ∈ Finset.range M,
              (1 / 2 : ℝ) * deriv (HNcore N) x =
          (1 / 2 : ℝ) *
            ((1 / (M : ℝ)) *
              ∑ N ∈ Finset.range M, deriv (HNcore N) x) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun N _ => by ring)
    have h2 :
        (1 / (M : ℝ)) *
            ((M : ℝ) * ((1 / 2 : ℝ) * deriv tailFn x)) =
          (1 / 2 : ℝ) * deriv tailFn x := by
      field_simp [hMne]
    rw [h1, h2]
  simp only [gCes, gSharp]
  rw [hreal]
  push_cast
  rw [Finset.mul_sum]

#print axioms cesaroCore_eq_average
#print axioms gCes_eq_average_gSharp

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
