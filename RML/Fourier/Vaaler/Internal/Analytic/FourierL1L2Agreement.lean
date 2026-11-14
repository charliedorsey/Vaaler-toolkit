module

public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology SchwartzMap
open scoped FourierTransform RealInnerProductSpace

namespace RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement

theorem integral_fourier_schwartz_smul_eq (f : ℝ → ℂ) (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, (𝓕 (fun y => g y)) x • f x)
      = ∫ ξ : ℝ, (g ξ) • (𝓕 f) ξ := by
  have hg : Integrable (fun y => g y) := g.integrable
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg hf
  simp only [flip_innerₗ] at key
  exact key

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

theorem fourierTransformₗᵢ_test_eq (T : Lp (α := ℝ) ℂ 2) (G : 𝓢(ℝ, ℂ)) :
    ((𝓕 T : Lp (α := ℝ) ℂ 2) : 𝓢'(ℝ, ℂ)) G
      = ∫ x : ℝ, (𝓕 G) x • (T : ℝ → ℂ) x := by
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq T]
  rw [TemperedDistribution.fourier_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

theorem fourierIntegral_ae_eq_fourierTransformₗᵢ {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 f := by
  set T : Lp (α := ℝ) ℂ 2 := hf2.toLp f with hT
  have hTf : (T : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hf1_li : LocallyIntegrable (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hf2_li : LocallyIntegrable (𝓕 f) volume :=
    (continuous_fourier_of_integrable hf).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hf1_li hf2_li ?_
  intro g g_smooth g_cpt
  have hG₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hG₂ : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hG₁.toSchwartzMap hG₂ with hG
  have hGval : ∀ x, (G : ℝ → ℂ) x = ((g x : ℝ) : ℂ) := fun x => rfl
  have hscal : ∀ (x : ℝ) (y : ℂ), (G : ℝ → ℂ) x • y = g x • y := by
    intro x y
    rw [hGval x]
    simp [Complex.real_smul]
  have hpair := fourierTransformₗᵢ_test_eq T G
  rw [MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
  calc
    (∫ x : ℝ, g x • (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) x)
        = ∫ x : ℝ, (G : ℝ → ℂ) x •
            (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ T)) x := by
          exact integral_congr_ae
            (Filter.Eventually.of_forall (fun x => (hscal x _).symm))
    _ = ∫ x : ℝ, (𝓕 (fun y => (G : ℝ → ℂ) y)) x • (T : ℝ → ℂ) x := hpair
    _ = ∫ x : ℝ, (𝓕 (fun y => (G : ℝ → ℂ) y)) x • f x := by
          refine integral_congr_ae ?_
          filter_upwards [hTf] with x hx
          rw [hx]
    _ = ∫ ξ : ℝ, (G : ℝ → ℂ) ξ • (𝓕 f) ξ :=
          integral_fourier_schwartz_smul_eq f hf G
    _ = ∫ x : ℝ, g x • 𝓕 f x :=
          integral_congr_ae
            (Filter.Eventually.of_forall (fun x => hscal x _))

#print axioms fourierIntegral_ae_eq_fourierTransformₗᵢ

end RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
