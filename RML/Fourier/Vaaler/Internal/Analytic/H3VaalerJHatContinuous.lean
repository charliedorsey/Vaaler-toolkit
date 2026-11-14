module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped ENNReal

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous

/-- Corrected continuous Vaaler transform. -/
def h3VaalerJHatCont (t : ℝ) : ℝ :=
  if 1 ≤ |t| then 0
  else if t = 0 then 1
  else Real.pi * |t| * (1 - |t|) * Real.cot (Real.pi * |t|) + |t|

def h3VaalerJHatContC (t : ℝ) : ℂ := (h3VaalerJHatCont t : ℂ)

@[simp] theorem h3VaalerJHatContC_apply (t : ℝ) :
    h3VaalerJHatContC t = (h3VaalerJHatCont t : ℂ) := rfl

theorem h3VaalerJHatCont_support {t : ℝ} (ht : 1 ≤ |t|) :
    h3VaalerJHatContC t = 0 := by
  rw [h3VaalerJHatContC, h3VaalerJHatCont, if_pos ht]
  norm_num

theorem h3VaalerJHatCont_support_subset :
    Function.support h3VaalerJHatContC ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  by_contra hmem
  apply ht
  rw [Set.mem_Icc, not_and_or] at hmem
  have h1 : 1 ≤ |t| := by
    rcases hmem with h | h
    · rw [le_abs]; right; linarith
    · rw [le_abs]; left; linarith
  exact h3VaalerJHatCont_support h1

theorem h3VaalerJHatCont_continuousAt_exterior {t : ℝ}
    (ht : 1 < |t|) :
    ContinuousAt h3VaalerJHatCont t := by
  have hcont : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t := continuousAt_const
  refine hcont.congr ?_
  have hopen : IsOpen {s : ℝ | 1 < |s|} := by
    have : {s : ℝ | 1 < |s|} =
        (fun s : ℝ => |s|) ⁻¹' Set.Ioi 1 := by
      ext s
      simp [Set.mem_Ioi]
    rw [this]
    exact continuous_abs.isOpen_preimage _ isOpen_Ioi
  filter_upwards [hopen.mem_nhds ht] with s hs
  rw [h3VaalerJHatCont, if_pos (le_of_lt hs)]

theorem h3VaalerJHatCont_continuousAt_interior {t : ℝ}
    (ht0 : t ≠ 0) (ht1 : |t| < 1) :
    ContinuousAt h3VaalerJHatCont t := by
  have hopen : IsOpen {s : ℝ | s ≠ 0 ∧ |s| < 1} := by
    exact isOpen_ne.inter (isOpen_lt continuous_abs continuous_const)
  have hmem : t ∈ {s : ℝ | s ≠ 0 ∧ |s| < 1} := ⟨ht0, ht1⟩
  have hsin : Real.sin (Real.pi * |t|) ≠ 0 := by
    have habs_pos : 0 < |t| := abs_pos.mpr ht0
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by positivity)
      (by
        have := mul_lt_mul_of_pos_left ht1 Real.pi_pos
        simpa using this))
  have habsCont : ContinuousAt (fun s : ℝ => |s|) t :=
    continuous_abs.continuousAt
  have hsinCont :
      ContinuousAt (fun s : ℝ => Real.sin (Real.pi * |s|)) t := by
    have h : ContinuousAt (fun u : ℝ => Real.sin (Real.pi * u)) |t| := by
      fun_prop
    exact h.comp habsCont
  have hcosCont :
      ContinuousAt (fun s : ℝ => Real.cos (Real.pi * |s|)) t := by
    have h : ContinuousAt (fun u : ℝ => Real.cos (Real.pi * u)) |t| := by
      fun_prop
    exact h.comp habsCont
  have hcot :
      ContinuousAt (fun s : ℝ => Real.cot (Real.pi * |s|)) t := by
    have hdiv :
        ContinuousAt
          (fun s : ℝ =>
            Real.cos (Real.pi * |s|) / Real.sin (Real.pi * |s|)) t :=
      hcosCont.div hsinCont hsin
    refine hdiv.congr ?_
    filter_upwards with s
    rw [Real.cot_eq_cos_div_sin]
  have hraw :
      ContinuousAt
        (fun s : ℝ =>
          Real.pi * |s| * (1 - |s|) *
            Real.cot (Real.pi * |s|) + |s|) t := by
    fun_prop
  refine hraw.congr ?_
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [h3VaalerJHatCont, if_neg (not_le.mpr hs.2), if_neg hs.1]

theorem h3VaalerJHatCont_continuousAt_zero :
    ContinuousAt h3VaalerJHatCont 0 := by
  let g : ℝ → ℝ :=
    fun s => (1 - |s|) * Real.cos (Real.pi * |s|) /
      Real.sinc (Real.pi * |s|) + |s|
  have hne : Real.sinc (Real.pi * |(0 : ℝ)|) ≠ 0 := by
    simp [Real.sinc_zero]
  have habs : ContinuousAt (fun s : ℝ => |s|) 0 :=
    continuous_abs.continuousAt
  have hsincC :
      ContinuousAt (fun s : ℝ => Real.sinc (Real.pi * |s|)) 0 := by
    fun_prop
  have hcosC :
      ContinuousAt (fun s : ℝ => Real.cos (Real.pi * |s|)) 0 := by
    fun_prop
  have hgC : ContinuousAt g 0 := by
    dsimp [g]
    exact ((((continuousAt_const.sub habs).mul hcosC).div hsincC hne).add habs)
  refine hgC.congr ?_
  have hopen : IsOpen {s : ℝ | |s| < 1} := by
    have : {s : ℝ | |s| < 1} =
        (fun s : ℝ => |s|) ⁻¹' Set.Iio 1 := by
      ext s
      simp [Set.mem_Iio]
    rw [this]
    exact continuous_abs.isOpen_preimage _ isOpen_Iio
  filter_upwards [hopen.mem_nhds (by simp : |(0 : ℝ)| < 1)] with s hs
  dsimp [g]
  by_cases hs0 : s = 0
  · subst s
    simp [h3VaalerJHatCont, Real.sinc_zero]
  · have habs_pos : 0 < |s| := abs_pos.mpr hs0
    have hpiabs : Real.pi * |s| ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (ne_of_gt habs_pos)
    rw [h3VaalerJHatCont, if_neg (not_le.mpr hs), if_neg hs0,
      Real.cot_eq_cos_div_sin, Real.sinc_of_ne_zero hpiabs]
    field_simp

theorem h3VaalerJHatCont_neg (t : ℝ) :
    h3VaalerJHatCont (-t) = h3VaalerJHatCont t := by
  unfold h3VaalerJHatCont
  simp only [abs_neg, neg_eq_zero]

private def gRef (s : ℝ) : ℝ :=
  |s| * Real.cos (Real.pi * |s|) /
      Real.sinc (Real.pi * (1 - |s|)) + |s|

private theorem gRef_one : gRef 1 = 0 := by
  unfold gRef
  norm_num [Real.sinc_zero, Real.cos_pi]

private theorem gRef_continuousAt_one : ContinuousAt gRef 1 := by
  have habs : ContinuousAt (fun s : ℝ => |s|) 1 :=
    continuous_abs.continuousAt
  have hsincC :
      ContinuousAt
        (fun s : ℝ => Real.sinc (Real.pi * (1 - |s|))) 1 := by
    fun_prop
  have hne : Real.sinc (Real.pi * (1 - |(1 : ℝ)|)) ≠ 0 := by
    norm_num [Real.sinc_zero]
  have hcosC :
      ContinuousAt (fun s : ℝ => Real.cos (Real.pi * |s|)) 1 := by
    fun_prop
  unfold gRef
  exact (((habs.mul hcosC).div hsincC hne).add habs)

private theorem raw_eq_gRef {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.pi * s * (1 - s) * Real.cot (Real.pi * s) + s =
      gRef s := by
  have hsabs : |s| = s := abs_of_pos hs0
  have h1s : 0 < 1 - s := by linarith
  have hsin_eq :
      Real.sin (Real.pi * s) =
        Real.sin (Real.pi * (1 - s)) := by
    have : Real.pi * (1 - s) =
        Real.pi - Real.pi * s := by ring
    rw [this, Real.sin_pi_sub]
  have hpi1s : Real.pi * (1 - s) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (ne_of_gt h1s)
  rw [Real.cot_eq_cos_div_sin, hsin_eq]
  unfold gRef
  rw [hsabs, Real.sinc_of_ne_zero hpi1s]
  field_simp

theorem h3VaalerJHatCont_continuousAt_one :
    ContinuousAt h3VaalerJHatCont 1 := by
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, ?_⟩
  · have hgWithin : ContinuousWithinAt gRef (Iic 1) 1 :=
      gRef_continuousAt_one.continuousWithinAt
    refine hgWithin.congr_of_eventuallyEq_of_mem ?_ (by simp)
    have hset :
        Set.Iic 1 ∩ Set.Ioo (1/2 : ℝ) 2 ∈ 𝓝[Set.Iic 1] (1 : ℝ) :=
      inter_mem_nhdsWithin (Set.Iic 1)
        (Ioo_mem_nhds (by norm_num) (by norm_num))
    refine Filter.eventuallyEq_of_mem hset ?_
    intro s hs
    rcases hs with ⟨hsle, ⟨hslo, _hshi⟩⟩
    have hsle' : s ≤ 1 := Set.mem_Iic.mp hsle
    rcases eq_or_lt_of_le hsle' with hseq | hslt
    · subst s
      rw [gRef_one]
      simp [h3VaalerJHatCont]
    · have hs0 : 0 < s := by linarith
      have hsabs : |s| = s := abs_of_pos hs0
      rw [h3VaalerJHatCont, if_neg (by rw [hsabs]; linarith),
        if_neg (ne_of_gt hs0), hsabs, raw_eq_gRef hs0 hslt]
  · have hconst :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici 1) 1 :=
      continuousWithinAt_const
    refine hconst.congr_of_eventuallyEq_of_mem ?_ (by simp)
    refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
    intro s hs
    have hsge : (1 : ℝ) ≤ s := hs
    have hsabs : 1 ≤ |s| := by
      rw [abs_of_nonneg (le_trans zero_le_one hsge)]
      exact hsge
    rw [h3VaalerJHatCont, if_pos hsabs]

theorem h3VaalerJHatCont_continuousAt_negOne :
    ContinuousAt h3VaalerJHatCont (-1) := by
  have hcomp :
      ContinuousAt (fun s : ℝ => h3VaalerJHatCont (-s)) (-1) := by
    have hneg : ContinuousAt (fun s : ℝ => -s) (-1) :=
      continuous_neg.continuousAt
    have h1 : ContinuousAt h3VaalerJHatCont (-(-1 : ℝ)) := by
      simpa using h3VaalerJHatCont_continuousAt_one
    exact h1.comp hneg
  refine hcomp.congr ?_
  filter_upwards with s
  exact h3VaalerJHatCont_neg s

theorem h3VaalerJHatCont_continuous :
    Continuous h3VaalerJHatCont := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy |t| 1 with hlt | heq | hgt
  · by_cases ht0 : t = 0
    · subst t
      exact h3VaalerJHatCont_continuousAt_zero
    · exact h3VaalerJHatCont_continuousAt_interior ht0 hlt
  · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp heq with h | h
    · rw [h]
      exact h3VaalerJHatCont_continuousAt_one
    · rw [h]
      exact h3VaalerJHatCont_continuousAt_negOne
  · exact h3VaalerJHatCont_continuousAt_exterior hgt

theorem h3VaalerJHatContC_continuous :
    Continuous h3VaalerJHatContC :=
  Complex.continuous_ofReal.comp h3VaalerJHatCont_continuous

theorem h3VaalerJHatContC_memLp_two :
    MemLp h3VaalerJHatContC 2 (volume : Measure ℝ) := by
  have hsupp : HasCompactSupport h3VaalerJHatContC := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    by_contra hne
    exact hx (h3VaalerJHatCont_support_subset hne)
  exact h3VaalerJHatContC_continuous.memLp_of_hasCompactSupport hsupp

#print axioms h3VaalerJHatCont_continuous
#print axioms h3VaalerJHatContC_memLp_two

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
