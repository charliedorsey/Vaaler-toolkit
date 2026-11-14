module

public import RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform

namespace RML.Fourier.Vaaler.Internal.Analytic.FourierPlancherelBridge

open RML.Fourier.Vaaler.Internal.Analytic.FourierL1L2Agreement

theorem fourierIntegral_eq_of_plancherel
    {f j : ℝ → ℂ}
    (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hj2 : MemLp j 2 (volume : Measure ℝ))
    (hjcont : Continuous j)
    (hL2 :
      MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)
        = hj2.toLp j) :
    𝓕 f = j := by
  have h1 :
      (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) : ℝ → ℂ)
        =ᵐ[volume] 𝓕 f :=
    fourierIntegral_ae_eq_fourierTransformₗᵢ hf1 hf2
  have h2 :
      (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)) : ℝ → ℂ)
        =ᵐ[volume] j := by
    rw [hL2]
    exact hj2.coeFn_toLp
  have hae : (𝓕 f) =ᵐ[volume] j := h1.symm.trans h2
  have hfcont : Continuous (𝓕 f) :=
    continuous_fourier_of_integrable hf1
  exact (hfcont.ae_eq_iff_eq volume hjcont).mp hae

theorem fourierIntegral_eq_of_plancherel_pointwise
    {f j : ℝ → ℂ}
    (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hj2 : MemLp j 2 (volume : Measure ℝ))
    (hjcont : Continuous j)
    (hL2 :
      MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f)
        = hj2.toLp j)
    (t : ℝ) :
    𝓕 f t = j t := by
  rw [fourierIntegral_eq_of_plancherel hf1 hf2 hj2 hjcont hL2]

#print axioms fourierIntegral_eq_of_plancherel

end RML.Fourier.Vaaler.Internal.Analytic.FourierPlancherelBridge
