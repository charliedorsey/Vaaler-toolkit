module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCoreFourier
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivLp
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroCore
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroPointwise
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDerivLp
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerTailFourier
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCoreFourier

theorem memLp_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume : Measure ℝ)) :
    MemLp (fun x => ∑ i ∈ s, f i x) 2 (volume : Measure ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (MemLp.zero' (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)) (ε := ℂ))
  | @insert a s ha ih =>
      have hfa : MemLp (f a) 2 (volume : Measure ℝ) :=
        hf a (by simp)
      have hfs : MemLp (fun x => ∑ i ∈ s, f i x) 2
          (volume : Measure ℝ) :=
        ih (fun i hi => hf i (by simp [hi]))
      have hadd := hfa.add hfs
      have heq :
          (fun x => ∑ i ∈ insert a s, f i x) =
            (f a + fun x => ∑ i ∈ s, f i x) := by
        funext x
        simp [Finset.sum_insert, ha, Pi.add_apply]
      rw [heq]
      exact hadd

theorem memLp_deriv_shift_sub (a : ℝ) :
    MemLp (fun x : ℝ => ((deriv h3VaalerK (x - a) : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by
  let h1 := memLp_deriv_h3VaalerK_complex_two.comp_measurePreserving
    ((volume : Measure ℝ).measurePreserving_sub_left (-a))
  let h2 := h1.comp_measurePreserving
    ((volume : Measure ℝ).measurePreserving_neg)
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h2

theorem memLp_deriv_shift_add (a : ℝ) :
    MemLp (fun x : ℝ => ((deriv h3VaalerK (x + a) : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by
  have h := memLp_deriv_shift_sub (-a)
  simpa only [sub_neg_eq_add] using h

theorem memLp_halfDerivHN (N : ℕ) :
    MemLp (halfDerivHN N) 2 (volume : Measure ℝ) := by
  let f : ℕ → ℝ → ℂ := fun m x =>
    ((deriv h3VaalerK (x - ((m : ℝ) + 1)) : ℝ) : ℂ) -
      ((deriv h3VaalerK (x + ((m : ℝ) + 1)) : ℝ) : ℂ)
  have hf : ∀ m ∈ Finset.range N,
      MemLp (f m) 2 (volume : Measure ℝ) := by
    intro m _
    exact (memLp_deriv_shift_sub ((m : ℝ) + 1)).sub
      (memLp_deriv_shift_add ((m : ℝ) + 1))
  have hsum := memLp_finset_sum (Finset.range N) f hf
  have hscaled := hsum.const_mul (1 / 2 : ℂ)
  have heq :
      halfDerivHN N =
        fun x => (1 / 2 : ℂ) * ∑ m ∈ Finset.range N, f m x := by
    funext x
    rw [halfDerivHN, deriv_HNcore_eq]
    push_cast
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [f]
    unfold dShift
    push_cast
    ring
  rw [heq]
  exact hscaled

theorem memLp_gCore (M : ℕ) :
    MemLp (gCore M) 2 (volume : Measure ℝ) := by
  let f : ℕ → ℝ → ℂ := fun N x => halfDerivHN N x
  have hf : ∀ N ∈ Finset.range M,
      MemLp (f N) 2 (volume : Measure ℝ) :=
    fun N _ => memLp_halfDerivHN N
  have hsum := memLp_finset_sum (Finset.range M) f hf
  have hscaled := hsum.const_mul (1 / (M : ℝ) : ℂ)
  have heq :
      gCore M =
        fun x => (1 / (M : ℝ) : ℂ) *
          ∑ N ∈ Finset.range M, f N x := by
    funext x
    exact gCore_eq_average M x
  rw [heq]
  exact hscaled

theorem gCes_eq_gCore_add_gTail (M : ℕ) :
    gCes M = fun x => gCore M x + gTail x := by
  funext x
  unfold gCes gCore gTail
  push_cast
  ring

theorem memLp_gCes (M : ℕ) :
    MemLp (gCes M) 2 (volume : Measure ℝ) := by
  rw [gCes_eq_gCore_add_gTail]
  exact (memLp_gCore M).add gTail_memLp_two

#print axioms memLp_deriv_shift_sub
#print axioms memLp_halfDerivHN
#print axioms memLp_gCore
#print axioms memLp_gCes

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerCesaroLp
