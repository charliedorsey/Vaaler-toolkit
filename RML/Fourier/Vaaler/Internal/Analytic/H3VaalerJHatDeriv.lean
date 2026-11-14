module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped ENNReal ContDiff

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDeriv

open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatContinuous
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv

def jhatD1 (t : ℝ) : ℝ :=
  Real.pi * (1 - 2 * t) *
      (Real.cos (Real.pi * t) / Real.sin (Real.pi * t))
    - Real.pi ^ 2 * t * (1 - t) / Real.sin (Real.pi * t) ^ 2 + 1

theorem sin_pi_ne_zero_interior {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Real.sin (Real.pi * t) ≠ 0 := by
  refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
  have := mul_lt_mul_of_pos_left h1 Real.pi_pos
  simpa using this

theorem hasDerivAt_pos_interior {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt h3VaalerJHatCont (jhatD1 t) t := by
  have hs := sin_pi_ne_zero_interior h0 h1
  have hlin : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (Real.pi * u))
      (Real.cos (Real.pi * t) * Real.pi) t :=
    (Real.hasDerivAt_sin (Real.pi * t)).comp t hlin
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (Real.pi * u))
      (-Real.sin (Real.pi * t) * Real.pi) t :=
    (Real.hasDerivAt_cos (Real.pi * t)).comp t hlin
  have hcot :
      HasDerivAt (fun u : ℝ =>
        Real.cos (Real.pi * u) / Real.sin (Real.pi * u))
      (((-Real.sin (Real.pi * t) * Real.pi) * Real.sin (Real.pi * t)
        - Real.cos (Real.pi * t) *
          (Real.cos (Real.pi * t) * Real.pi))
        / Real.sin (Real.pi * t) ^ 2) t :=
    hcos.div hsin hs
  have hP : HasDerivAt (fun u : ℝ => Real.pi * u * (1 - u))
      (Real.pi * (1 - 2 * t)) t := by
    have h1' : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi t := hlin
    have h2' : HasDerivAt (fun u : ℝ => (1 - u)) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    exact (h1'.mul h2').congr_deriv (by ring)
  have hfull := (hP.mul hcot).add (hasDerivAt_id t)
  have hraw : HasDerivAt
      (fun u : ℝ =>
        Real.pi * u * (1-u) *
          (Real.cos (Real.pi*u) / Real.sin (Real.pi*u)) + u)
      (jhatD1 t) t := by
    refine hfull.congr_deriv ?_
    unfold jhatD1
    have hpyth :
        Real.sin (Real.pi*t)^2 + Real.cos (Real.pi*t)^2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi*t)
    field_simp [hs]
    linear_combination (-(Real.pi^2 * t * (1-t))) * hpyth
  refine hraw.congr_of_eventuallyEq ?_
  have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
  filter_upwards [hopen.mem_nhds ⟨h0,h1⟩] with u hu
  have huabs : |u| = u := abs_of_pos hu.1
  rw [h3VaalerJHatCont, if_neg (not_le.mpr (by simpa [huabs] using hu.2)),
    if_neg (ne_of_gt hu.1), huabs, Real.cot_eq_cos_div_sin]

def psi (t : ℝ) : ℝ :=
  Real.cos (Real.pi * t) / Real.sinc (Real.pi * t)

def Jext (t : ℝ) : ℝ := (1-t) * psi t + t

theorem contDiffAt_psi_zero : ContDiffAt ℝ ∞ psi 0 := by
  have hnum : ContDiffAt ℝ ∞ (fun t : ℝ => Real.cos (Real.pi*t)) 0 :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun t : ℝ => Real.sinc (Real.pi*t)) 0 :=
    (contDiff_sinc.comp (contDiff_const.mul contDiff_id)).contDiffAt
  exact hnum.div hden (by simp)

theorem psi_zero : psi 0 = 1 := by simp [psi]

theorem psi_neg (t : ℝ) : psi (-t) = psi t := by
  unfold psi
  rw [mul_neg, Real.cos_neg, Real.sinc_neg]

theorem deriv_psi_zero : deriv psi 0 = 0 := by
  have hd : HasDerivAt psi (deriv psi 0) 0 :=
    (contDiffAt_psi_zero.differentiableAt (by decide)).hasDerivAt
  have hn : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) 0 := by
    have h := (hasDerivAt_id (0:ℝ)).neg
    exact h.congr_of_eventuallyEq (by filter_upwards with x; rfl)
  have hd' : HasDerivAt psi (deriv psi 0) (-0) := by simpa using hd
  have hc := hd'.comp 0 hn
  have heq : (fun x : ℝ => psi (-x)) = psi := by
    funext x
    exact psi_neg x
  change HasDerivAt (fun x : ℝ => psi (-x)) (deriv psi 0 * (-1)) 0 at hc
  rw [heq] at hc
  linarith [hc.deriv]

theorem Jext_eq_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Jext t = h3VaalerJHatCont t := by
  have hs := sin_pi_ne_zero_interior h0 h1
  have ht0 : t ≠ 0 := ne_of_gt h0
  have hpit : Real.pi*t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht0
  unfold Jext psi
  rw [Real.sinc_of_ne_zero hpit]
  have hat : |t| = t := abs_of_pos h0
  rw [h3VaalerJHatCont, if_neg (not_le.mpr (by simpa [hat] using h1)),
    if_neg ht0, hat, Real.cot_eq_cos_div_sin]
  field_simp [hs, Real.pi_ne_zero, ht0]

theorem contDiffAt_Jext_zero : ContDiffAt ℝ ∞ Jext 0 := by
  unfold Jext
  exact ((contDiffAt_const.sub contDiffAt_id).mul contDiffAt_psi_zero).add contDiffAt_id

theorem deriv_Jext_zero : deriv Jext 0 = 0 := by
  have hp : HasDerivAt psi (deriv psi 0) 0 :=
    (contDiffAt_psi_zero.differentiableAt (by decide)).hasDerivAt
  have hlin : HasDerivAt (fun x : ℝ => 1-x) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
  have h := (hlin.mul hp).add (hasDerivAt_id (0:ℝ))
  change HasDerivAt Jext ((-1)*psi 0 + (1-0)*deriv psi 0 + 1) 0 at h
  rw [h.deriv, psi_zero, deriv_psi_zero]
  ring

def jhatD1Ext (u : ℝ) : ℝ :=
  if u = 0 ∨ u = 1 then 0 else jhatD1 u

theorem jhatD1Ext_interior {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    jhatD1Ext u = jhatD1 u := by
  simp [jhatD1Ext, ne_of_gt h0, ne_of_lt h1]

theorem Jext_eventuallyEq_pos {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    Jext =ᶠ[𝓝 u] h3VaalerJHatCont := by
  have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
  filter_upwards [hopen.mem_nhds ⟨h0,h1⟩] with v hv
  exact Jext_eq_pos hv.1 hv.2

theorem deriv_Jext_eq_jhatD1 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    deriv Jext u = jhatD1 u := by
  rw [(Jext_eventuallyEq_pos h0 h1).deriv_eq]
  exact (hasDerivAt_pos_interior h0 h1).deriv

theorem continuousAt_deriv_Jext_zero :
    ContinuousAt (deriv Jext) 0 := by
  have h : ContDiffAt ℝ 1 (deriv Jext) 0 :=
    contDiffAt_Jext_zero.derivWithin (by decide)
  exact h.continuousAt

theorem continuousWithinAt_jhatD1Ext_zero :
    ContinuousWithinAt jhatD1Ext (Set.Icc (0:ℝ) 1) 0 := by
  have hwithin : ContinuousWithinAt (deriv Jext) (Set.Icc (0:ℝ) 1) 0 :=
    continuousAt_deriv_Jext_zero.continuousWithinAt
  have hlim :
      Tendsto (deriv Jext) (𝓝[Set.Icc (0:ℝ) 1] 0)
        (𝓝 (0 : ℝ)) := by
    simpa [ContinuousWithinAt, deriv_Jext_zero] using hwithin
  have heq : jhatD1Ext =ᶠ[𝓝[Set.Icc (0:ℝ) 1] 0] deriv Jext := by
    have hsub : Set.Ico (0:ℝ) 1 ∈ 𝓝[Set.Icc (0:ℝ) 1] 0 := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (1:ℝ), isOpen_Iio, by norm_num, by
        intro x hx
        exact ⟨hx.2.1, hx.1⟩⟩
    filter_upwards [hsub] with x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x
      simp [jhatD1Ext, deriv_Jext_zero]
    · rw [jhatD1Ext_interior h hx.2, deriv_Jext_eq_jhatD1 h hx.2]
  rw [ContinuousWithinAt]
  have hval : jhatD1Ext 0 = 0 := by simp [jhatD1Ext]
  rw [hval]
  exact hlim.congr' heq.symm

theorem jhatD1_reflect (u : ℝ) :
    jhatD1 (1-u) = jhatD1 u := by
  have hc : Real.cos (Real.pi*(1-u)) = -Real.cos (Real.pi*u) := by
    rw [mul_sub, mul_one, Real.cos_pi_sub]
  have hs : Real.sin (Real.pi*(1-u)) = Real.sin (Real.pi*u) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  unfold jhatD1
  rw [hc,hs]
  ring

theorem jhatD1Ext_reflect (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    jhatD1Ext (1-u) = jhatD1Ext u := by
  rcases eq_or_ne u 0 with rfl | h0
  · simp [jhatD1Ext]
  rcases eq_or_ne u 1 with rfl | h1
  · simp [jhatD1Ext]
  have h01 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
  have h10 : u < 1 := lt_of_le_of_ne hu.2 h1
  rw [jhatD1Ext_interior (by linarith) (by linarith),
      jhatD1Ext_interior h01 h10, jhatD1_reflect]

theorem continuousWithinAt_jhatD1Ext_one :
    ContinuousWithinAt jhatD1Ext (Set.Icc (0:ℝ) 1) 1 := by
  have h0 := continuousWithinAt_jhatD1Ext_zero
  have hreflect :
      Tendsto (fun u : ℝ => 1-u)
        (𝓝[Set.Icc (0:ℝ) 1] 1)
        (𝓝[Set.Icc (0:ℝ) 1] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous (fun u : ℝ => 1-u) := continuous_const.sub continuous_id
      have hcont : Tendsto (fun u : ℝ => 1-u) (𝓝 (1:ℝ)) (𝓝 (0:ℝ)) := by
        simpa using hc.tendsto (1 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hc : Tendsto (fun u => jhatD1Ext (1-u))
      (𝓝[Set.Icc (0:ℝ) 1] 1) (𝓝 (jhatD1Ext 0)) :=
    h0.tendsto.comp hreflect
  have heq : jhatD1Ext =ᶠ[𝓝[Set.Icc (0:ℝ) 1] 1]
      (fun u => jhatD1Ext (1-u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (jhatD1Ext_reflect u hu).symm
  rw [ContinuousWithinAt]
  have hvals : jhatD1Ext 1 = jhatD1Ext 0 := by simp [jhatD1Ext]
  rw [hvals]
  exact hc.congr' heq.symm


def dJ (t : ℝ) : ℝ :=
  if 1 ≤ |t| then 0
  else if t = 0 then 0
  else if 0 < t then jhatD1 t else -jhatD1 (-t)

theorem dJ_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : dJ t = jhatD1 t := by
  have hat : |t| = t := abs_of_pos h0
  simp [dJ, hat, not_le.mpr h1, ne_of_gt h0, h0]

theorem dJ_neg_interior {t : ℝ} (hm1 : -1 < t) (h0 : t < 0) :
    dJ t = -jhatD1 (-t) := by
  have hat : |t| = -t := abs_of_neg h0
  have hlt : -t < 1 := by linarith
  have hp : ¬ 0 < t := by linarith
  simp [dJ, hat, not_le.mpr hlt, ne_of_lt h0, hp]

theorem dJ_neg (t : ℝ) : dJ (-t) = -dJ t := by
  unfold dJ
  by_cases h1 : 1 ≤ |t|
  · simp [abs_neg, h1]
  by_cases h0 : t = 0
  · subst t; simp
  by_cases hp : 0 < t
  · have hn : ¬ 0 < -t := by linarith
    have hnt0 : -t ≠ 0 := neg_ne_zero.mpr h0
    simp [abs_neg, h1, h0, hnt0, hp, hn]
  · have htn : t < 0 := lt_of_le_of_ne (le_of_not_gt hp) h0
    have hnp : 0 < -t := by linarith
    have hnt0 : -t ≠ 0 := neg_ne_zero.mpr h0
    simp [abs_neg, h1, h0, hnt0, hp, hnp]

theorem tendsto_dJ_zero_right :
    Tendsto dJ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hIcc : Set.Icc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio (1:ℝ), isOpen_Iio, by norm_num, by
      intro x hx; exact ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) 1] 0 :=
    nhdsWithin_le_iff.mpr hIcc
  have hlim : Tendsto jhatD1Ext (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := continuousWithinAt_jhatD1Ext_zero.tendsto.mono_left hle
    simpa [jhatD1Ext] using h
  refine hlim.congr' ?_
  have hsmall : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio (1:ℝ), isOpen_Iio, by norm_num, by
      intro x hx; exact ⟨hx.2, hx.1⟩⟩
  filter_upwards [hsmall] with t ht
  rw [dJ_pos ht.1 ht.2, jhatD1Ext_interior ht.1 ht.2]

theorem continuousAt_dJ_zero : ContinuousAt dJ 0 := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · have hnegfilter : Tendsto Neg.neg (𝓝[<] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
    have hcomp : Tendsto (fun t : ℝ => dJ (-t)) (𝓝[<] 0) (𝓝 0) :=
      tendsto_dJ_zero_right.comp hnegfilter
    have hneg := hcomp.neg
    have heq : (fun t : ℝ => -dJ (-t)) = dJ := by
      funext t
      rw [dJ_neg]
      simp
    rw [heq] at hneg
    rw [← continuousWithinAt_Iio_iff_Iic]
    simpa [ContinuousWithinAt, dJ] using hneg
  · rw [← continuousWithinAt_Ioi_iff_Ici]
    simpa [ContinuousWithinAt, dJ] using tendsto_dJ_zero_right

theorem tendsto_dJ_one_left :
    Tendsto dJ (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hIcc : Set.Icc (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi (0:ℝ), isOpen_Ioi, by norm_num, by
      intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  have hle : 𝓝[<] (1:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) 1] 1 :=
    nhdsWithin_le_iff.mpr hIcc
  have hlim : Tendsto jhatD1Ext (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have h := continuousWithinAt_jhatD1Ext_one.tendsto.mono_left hle
    simpa [jhatD1Ext] using h
  refine hlim.congr' ?_
  have hsmall : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi (0:ℝ), isOpen_Ioi, by norm_num, by
      intro x hx; exact ⟨hx.1, hx.2⟩⟩
  filter_upwards [hsmall] with t ht
  rw [dJ_pos ht.1 ht.2, jhatD1Ext_interior ht.1 ht.2]

theorem hasDerivAt_one : HasDerivAt h3VaalerJHatCont 0 1 := by
  have hleft : HasDerivWithinAt h3VaalerJHatCont 0 (Set.Iic (1:ℝ)) 1 := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (s := Set.Ioo (0:ℝ) 1) (e := 0)
    · intro x hx
      exact (hasDerivAt_pos_interior hx.1 hx.2).differentiableAt.differentiableWithinAt
    · exact h3VaalerJHatCont_continuous.continuousAt.continuousWithinAt
    · have h : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
        rw [mem_nhdsWithin]
        exact ⟨Set.Ioi (0:ℝ), isOpen_Ioi, by norm_num, by
          intro x hx; exact ⟨hx.1, hx.2⟩⟩
      exact h
    · have heq : (fun x : ℝ => deriv h3VaalerJHatCont x) =ᶠ[𝓝[<] 1] dJ := by
        have hsmall : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi (0:ℝ), isOpen_Ioi, by norm_num, by
            intro x hx; exact ⟨hx.1, hx.2⟩⟩
        filter_upwards [hsmall] with x hx
        rw [(hasDerivAt_pos_interior hx.1 hx.2).deriv, dJ_pos hx.1 hx.2]
      exact tendsto_dJ_one_left.congr' heq.symm
  have hright : HasDerivWithinAt h3VaalerJHatCont 0 (Set.Ici (1:ℝ)) 1 := by
    have hc : HasDerivWithinAt (fun _ : ℝ => (0:ℝ)) 0 (Set.Ici (1:ℝ)) 1 :=
      (hasDerivAt_const (1:ℝ) (0:ℝ)).hasDerivWithinAt
    refine hc.congr ?_ ?_
    · intro x hx
      rw [h3VaalerJHatCont, if_pos]
      rw [abs_of_nonneg (le_trans zero_le_one hx)]
      exact hx
    · simp [h3VaalerJHatCont]
  simpa using hleft.union hright

theorem hasDerivAt_negOne : HasDerivAt h3VaalerJHatCont 0 (-1) := by
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) (-1) := by
    have h := (hasDerivAt_id (-1:ℝ)).neg
    exact h.congr_of_eventuallyEq (by filter_upwards with x; rfl)
  have houter : HasDerivAt h3VaalerJHatCont 0 (-(-1 : ℝ)) := by simpa using hasDerivAt_one
  have hc := houter.comp (-1) hneg
  have heq : (fun x : ℝ => h3VaalerJHatCont (-x)) = h3VaalerJHatCont := by
    funext x
    exact h3VaalerJHatCont_neg x
  change HasDerivAt (fun x : ℝ => h3VaalerJHatCont (-x)) (0 * (-1)) (-1) at hc
  rw [heq] at hc
  simpa using hc

theorem hasDerivAt_off_zero (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt h3VaalerJHatCont (dJ y) y := by
  by_cases hout : 1 < |y|
  · have hopen : IsOpen {x : ℝ | 1 < |x|} :=
      isOpen_lt continuous_const continuous_abs
    have hloc : h3VaalerJHatCont =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [hopen.mem_nhds hout] with x hx
      rw [h3VaalerJHatCont, if_pos (le_of_lt hx)]
    have hd := (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq hloc
    have hdj : dJ y = 0 := by
      simp [dJ, le_of_lt hout]
    simpa [hdj] using hd
  · have hle : |y| ≤ 1 := le_of_not_gt hout
    rcases lt_trichotomy y 0 with hyn | hy0 | hyp
    · have hm1 : -1 ≤ y := (abs_le.mp hle).1
      rcases eq_or_lt_of_le hm1 with hEq | hLt
      · subst y
        simpa [dJ] using hasDerivAt_negOne
      · have hp : 0 < -y := by linarith
        have hp1 : -y < 1 := by linarith
        have hnegmap : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) y := by
          have h := (hasDerivAt_id y).neg
          exact h.congr_of_eventuallyEq (by filter_upwards with x; rfl)
        have hc := (hasDerivAt_pos_interior hp hp1).comp y hnegmap
        have heq : (fun x : ℝ => h3VaalerJHatCont (-x)) = h3VaalerJHatCont := by
          funext x; exact h3VaalerJHatCont_neg x
        change HasDerivAt (fun x : ℝ => h3VaalerJHatCont (-x))
          (jhatD1 (-y) * (-1)) y at hc
        rw [heq] at hc
        rw [dJ_neg_interior hLt hyn]
        simpa using hc
    · exact (hy hy0).elim
    · have hy1 : y ≤ 1 := (abs_le.mp hle).2
      rcases eq_or_lt_of_le hy1 with hEq | hLt
      · subst y
        simpa [dJ] using hasDerivAt_one
      · rw [dJ_pos hyp hLt]
        exact hasDerivAt_pos_interior hyp hLt

theorem hasDerivAt_zero : HasDerivAt h3VaalerJHatCont 0 0 := by
  have h := hasDerivAt_of_hasDerivAt_of_ne
    (f := h3VaalerJHatCont) (g := dJ) (x := (0:ℝ))
    hasDerivAt_off_zero
    h3VaalerJHatCont_continuous.continuousAt
    continuousAt_dJ_zero
  simpa [dJ] using h

theorem differentiable_h3VaalerJHatCont : Differentiable ℝ h3VaalerJHatCont := by
  intro x
  by_cases hx : x = 0
  · subst x; exact hasDerivAt_zero.differentiableAt
  · exact (hasDerivAt_off_zero x hx).differentiableAt

theorem deriv_eq_dJ (x : ℝ) : deriv h3VaalerJHatCont x = dJ x := by
  by_cases hx : x = 0
  · subst x
    rw [hasDerivAt_zero.deriv]
    simp [dJ]
  · exact (hasDerivAt_off_zero x hx).deriv

#print axioms hasDerivAt_one
#print axioms hasDerivAt_zero
#print axioms differentiable_h3VaalerJHatCont
#print axioms deriv_eq_dJ

#print axioms continuousWithinAt_jhatD1Ext_zero
#print axioms continuousWithinAt_jhatD1Ext_one

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerJHatDeriv
