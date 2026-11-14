module

public import RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
public import Mathlib.Analysis.Analytic.Basic

@[expose] public section

noncomputable section

open Real Filter Topology
open scoped ContDiff

namespace RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv

open RML.Fourier.Vaaler.Internal
open RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelFourier
open RML.Fourier.Vaaler.Internal.Analytic.SincSquare

theorem analyticAt_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    rw [Real.sinc_eq_dslope]
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have hden : AnalyticAt ℝ (fun y : ℝ => y) x := analyticAt_id
    have hnum : AnalyticAt ℝ Real.sin x := Real.analyticAt_sin
    have h : AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x :=
      hnum.div hden hx
    refine h.congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

theorem contDiff_sinc : ContDiff ℝ ∞ Real.sinc :=
  contDiff_iff_contDiffAt.2
    (fun x => (analyticAt_sinc x).contDiffAt.of_le le_top)

theorem contDiff_sincSqPi : ContDiff ℝ ∞ sincSqPi := by
  unfold sincSqPi
  exact
    ((contDiff_sinc.comp
      (contDiff_const.mul contDiff_id)).pow 2)

theorem contDiff_h3VaalerK : ContDiff ℝ ∞ h3VaalerK := by
  rw [h3VaalerK_eq_sincSqPi_fun]
  exact contDiff_sincSqPi

theorem hasDerivAt_h3VaalerK_offZero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt h3VaalerK
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3) x := by
  have hsinpi : HasDerivAt
      (fun z : ℝ => Real.sin (Real.pi * z))
      (Real.cos (Real.pi * x) * Real.pi) x := by
    have hinner : HasDerivAt (fun z : ℝ => Real.pi * z) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    exact (Real.hasDerivAt_sin (Real.pi * x)).comp x hinner
  have hdiv : HasDerivAt
      (fun z : ℝ => Real.sin (Real.pi * z) / Real.pi)
      (Real.cos (Real.pi * x) * Real.pi / Real.pi) x :=
    hsinpi.div_const Real.pi
  have hsq : HasDerivAt
      (fun z : ℝ => (Real.sin (Real.pi * z) / Real.pi) ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
        (Real.cos (Real.pi * x) * Real.pi / Real.pi)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hinv : HasDerivAt (fun z : ℝ => z⁻¹ ^ 2)
      (-2 * x⁻¹ ^ 3) x := by
    have hh : HasDerivAt (fun z : ℝ => z⁻¹) (-(x⁻¹ ^ 2)) x := by
      have h := hasDerivAt_inv hx
      simpa [pow_two] using h
    refine (hh.pow 2).congr_deriv ?_
    ring
  have hprod : HasDerivAt
      (fun z : ℝ =>
        (Real.sin (Real.pi * z) / Real.pi) ^ 2 * z⁻¹ ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2
        + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-2 * x⁻¹ ^ 3)) x := by
    refine (hsq.mul hinv).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  have hbranch :
      h3VaalerK =ᶠ[nhds x]
        (fun z : ℝ =>
          (Real.sin (Real.pi * z) / Real.pi) ^ 2 * z⁻¹ ^ 2) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    simp [h3VaalerK, hz]
    ring
  have hraw : HasDerivAt
      (fun z : ℝ =>
        (Real.sin (Real.pi * z) / Real.pi) ^ 2 * z⁻¹ ^ 2)
      (2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3) x := by
    convert hprod using 1 <;> ring
  exact hraw.congr_of_eventuallyEq hbranch

theorem deriv_h3VaalerK_offZero {x : ℝ} (hx : x ≠ 0) :
    deriv h3VaalerK x =
      2 * (Real.sin (Real.pi * x) / Real.pi) *
          (Real.cos (Real.pi * x) * Real.pi / Real.pi) * x⁻¹ ^ 2
        - 2 * (Real.sin (Real.pi * x) / Real.pi) ^ 2 * x⁻¹ ^ 3 :=
  (hasDerivAt_h3VaalerK_offZero hx).deriv

#print axioms contDiff_h3VaalerK
#print axioms deriv_h3VaalerK_offZero

end RML.Fourier.Vaaler.Internal.Analytic.H3VaalerKernelDeriv
