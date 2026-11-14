module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDerivLp

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDeriv
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous

theorem continuousAt_jhatD1_interior {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ContinuousAt jhatD1 t := by
  have hs := sin_pi_ne_zero_interior h0 h1
  have hlin : ContinuousAt (fun u : ℝ => Real.pi * u) t :=
    (continuous_const.mul continuous_id).continuousAt
  have hsin : ContinuousAt (fun u : ℝ => Real.sin (Real.pi * u)) t :=
    Real.continuous_sin.continuousAt.comp hlin
  have hcos : ContinuousAt (fun u : ℝ => Real.cos (Real.pi * u)) t :=
    Real.continuous_cos.continuousAt.comp hlin
  unfold jhatD1
  exact
    (((continuousAt_const.mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))).mul
        (hcos.div hsin hs)).sub
      ((((continuousAt_const.pow 2).mul continuousAt_id).mul
          (continuousAt_const.sub continuousAt_id)).div
        (hsin.pow 2) (pow_ne_zero 2 hs))).add continuousAt_const

theorem continuousOn_jhatD1Ext :
    ContinuousOn jhatD1Ext (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst t
    exact continuousWithinAt_jhatD1Ext_zero
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst t
    exact continuousWithinAt_jhatD1Ext_one
  · have hc := continuousAt_jhatD1_interior h0 h1
    have heq : jhatD1Ext =ᶠ[𝓝 t] jhatD1 := by
      have hopen : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
      filter_upwards [hopen.mem_nhds ⟨h0,h1⟩] with s hs
      exact jhatD1Ext_interior hs.1 hs.2
    exact (hc.congr (heq.symm)).continuousWithinAt

theorem exists_bound_jhatD1Ext :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |jhatD1Ext u| ≤ B := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have habscont : ContinuousOn (fun u => |jhatD1Ext u|) (Set.Icc (0 : ℝ) 1) :=
    continuous_abs.comp_continuousOn continuousOn_jhatD1Ext
  obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn habscont).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu
  have hmem : |jhatD1Ext u| ∈
      (fun z => |jhatD1Ext z|) '' Set.Icc (0 : ℝ) 1 :=
    ⟨u, hu, rfl⟩
  exact le_trans (hC hmem) (le_max_left _ _)

theorem dJ_support_subset :
    Function.support dJ ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or] at hmem
  have h1 : 1 ≤ |t| := by
    rcases hmem with h | h
    · rw [le_abs]
      right
      linarith
    · rw [le_abs]
      left
      linarith
  exact ht (by simp [dJ, h1])

theorem dJ_measurable : Measurable dJ := by
  have hder : Measurable (deriv h3VaalerJHatCont) :=
    measurable_deriv h3VaalerJHatCont
  have heq : deriv h3VaalerJHatCont = dJ := by
    funext x
    exact deriv_eq_dJ x
  rwa [heq] at hder

theorem exists_bound_dJ :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |dJ t| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_jhatD1Ext
  refine ⟨B, hB0, ?_⟩
  intro t
  by_cases h1 : 1 ≤ |t|
  · simp [dJ, h1, hB0]
  have hlt : |t| < 1 := not_le.mp h1
  by_cases h0 : t = 0
  · subst t
    simp [dJ, hB0]
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hu0 : 0 ≤ -t := by linarith
    have hu1 : -t ≤ 1 := by
      have hat : |t| = -t := abs_of_neg hneg
      rw [hat] at hlt
      linarith
    have hat : |t| = -t := abs_of_neg hneg
    have hltneg : -t < 1 := by simpa [hat] using hlt
    have hext : jhatD1Ext (-t) = jhatD1 (-t) := by
      exact jhatD1Ext_interior (by linarith) hltneg
    rw [dJ_neg_interior (by linarith) hneg, ← hext, abs_neg]
    exact hB (-t) ⟨hu0, hu1⟩
  · have hu0 : 0 ≤ t := le_of_lt hpos
    have hu1 : t ≤ 1 := by
      have hat : |t| = t := abs_of_pos hpos
      rw [hat] at hlt
      linarith
    have hat : |t| = t := abs_of_pos hpos
    have hltpos : t < 1 := by simpa [hat] using hlt
    have hext : jhatD1Ext t = jhatD1 t :=
      jhatD1Ext_interior hpos hltpos
    rw [dJ_pos hpos hltpos, ← hext]
    exact hB t ⟨hu0, hu1⟩

def dJC (t : ℝ) : ℂ := (dJ t : ℂ)

theorem dJC_aestronglyMeasurable :
    AEStronglyMeasurable dJC (volume : Measure ℝ) :=
  (Complex.measurable_ofReal.comp dJ_measurable).aestronglyMeasurable

theorem dJC_hasCompactSupport : HasCompactSupport dJC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  by_contra hne
  have hd : dJ t ≠ 0 := by
    intro hz
    apply hne
    simp [dJC, hz]
  exact ht (dJ_support_subset (Function.mem_support.mpr hd))

theorem dJC_memLp (p : ℝ≥0∞) :
    MemLp dJC p (volume : Measure ℝ) := by
  obtain ⟨B, _, hB⟩ := exists_bound_dJ
  refine dJC_hasCompactSupport.memLp_of_bound dJC_aestronglyMeasurable B ?_
  filter_upwards with t
  rw [dJC, Complex.norm_real, Real.norm_eq_abs]
  exact hB t

theorem dJC_integrable : Integrable dJC (volume : Measure ℝ) := by
  exact memLp_one_iff_integrable.mp (dJC_memLp 1)

theorem dJC_memLp_two : MemLp dJC 2 (volume : Measure ℝ) :=
  dJC_memLp 2

theorem h3VaalerJHatContC_integrable :
    Integrable h3VaalerJHatContC (volume : Measure ℝ) := by
  have hsupp : HasCompactSupport h3VaalerJHatContC := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro t ht
    by_contra hne
    exact ht (h3VaalerJHatCont_support_subset (Function.mem_support.mpr hne))
  exact h3VaalerJHatContC_continuous.integrable_of_hasCompactSupport hsupp

theorem differentiable_h3VaalerJHatContC :
    Differentiable ℝ h3VaalerJHatContC := by
  intro t
  have hR : HasDerivAt h3VaalerJHatCont (dJ t) t := by
    rw [← deriv_eq_dJ t]
    exact (differentiable_h3VaalerJHatCont t).hasDerivAt
  exact hR.ofReal_comp.differentiableAt

theorem deriv_h3VaalerJHatContC (t : ℝ) :
    deriv h3VaalerJHatContC t = dJC t := by
  have hR : HasDerivAt h3VaalerJHatCont (dJ t) t := by
    rw [← deriv_eq_dJ t]
    exact (differentiable_h3VaalerJHatCont t).hasDerivAt
  exact hR.ofReal_comp.deriv

theorem deriv_h3VaalerJHatContC_integrable :
    Integrable (deriv h3VaalerJHatContC) (volume : Measure ℝ) := by
  have heq : deriv h3VaalerJHatContC = dJC := by
    funext t
    exact deriv_h3VaalerJHatContC t
  rw [heq]
  exact dJC_integrable

#print axioms dJC_memLp_two
#print axioms dJC_integrable
#print axioms differentiable_h3VaalerJHatContC
#print axioms deriv_h3VaalerJHatContC_integrable

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDerivLp
